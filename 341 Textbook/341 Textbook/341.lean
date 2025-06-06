import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic


-- CHAPTER 8 : Sequences of Real Numbers

section  Definitions

variable {α : Type*}

-- Def 8.1
def convto (a : ℕ → ℝ) (L : ℝ) :=  
  ∀ ε > 0, ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |a n - L| < ε 

def converges (a : ℕ → ℝ) := 
  ∃ (L : ℝ), convto a L

-- Def 8.2
def boundedby (a : α → ℝ) (M : ℝ) :=
  ∀ n : α, |a n| < M 

def bounded (a : α → ℝ) :=
  ∃ (M : ℝ), boundedby a M

-- Def 8.3
def cauchy (a : ℕ → ℝ) :=
  ∀ (ε : ℝ), ε > 0 → ∃ (N : ℕ), ∀ (m n : ℕ) , m ≥ N → n ≥ N → m ≥ n → |a m - a n| < ε 




end Definitions

section  Theorems
variable {n : ℕ}
variable {A L K: ℝ}
variable {a b : ℕ → ℝ}

theorem converges_of_convto (h : convto a L) : converges a := ⟨L,h⟩ 

theorem bounded_of_boundedby (h : boundedby a K) : bounded a := ⟨K,h⟩


theorem convto_constant : convto (fun _ ↦ L) L := by 
  intro ε εpos; use 0; intro n hn
  simp; exact εpos

-- Prop 8.1
theorem convto_unique (h1 : convto a L) (h2 : convto a K) : L = K := by 
  have h: ∀ ε > 0, |L - K| < ε  := by 
    intro ε εpos
    obtain ⟨N,hN⟩ := h1 (ε/2) (by linarith)
    obtain ⟨M, hM⟩ := h2 (ε/2) (by linarith)
    set m := max N M
    have hm : m = max N M := rfl 
    have mgeN : m ≥ N := by rw[hm]; apply le_max_left 
    have mgeM : m ≥ M := by rw[hm]; apply le_max_right
    calc
      |L - K| = |(L - a m) + (a m - K)| := by group
      _ ≤ |L - a m| + |a m - K| := by apply abs_add
      _ = |-(a m - L)| + |a m - K| := by group
      _ = |a m - L| + |a m - K| := by rw[abs_neg]
      _ < (ε/2) + (ε/2) := by apply add_lt_add; exact hN m mgeN; exact hM m mgeM
      _ = ε := by ring
  have h': |L - K| ≤ 0 := by
    apply le_of_forall_pos_le_add; simp; intro a b; apply le_of_lt; exact h a b
  have : |L - K| = 0 := by apply le_antisymm h' ; apply abs_nonneg
  apply abs_eq_zero.1 at this; linarith


-- Prop 8.2 
theorem bounded_of_converges (h : converges a) : bounded a := by 
  obtain ⟨L, h⟩ := h
  obtain ⟨N, h'⟩ := h 1 zero_lt_one
  let M := max (∑ i ≤ N, |a i|+1) (|L| + 1)
  have hM : M = max (∑ i ≤ N, |a i| + 1) (|L| + 1) := rfl
  use M; intro n; rw[hM]
  by_cases hn: n < N
  apply lt_max_of_lt_left; rw[← add_zero |a n|]; apply add_lt_add_of_le_of_lt
  apply le_of_sub_nonneg
  clear M hM h h' L
  have h : n ∈ Finset.Iic N := Finset.mem_Iic.mpr (le_of_lt hn)
  calc
    ∑ i ∈ Finset.Iic N, |a i| - |a n| = ∑ i ∈ Finset.Iic N \ {n}, |a i| := by
      rw [← Finset.sum_sdiff, Finset.sdiff_singleton_eq_erase]; simp; exact Finset.singleton_subset_iff.2 h
    _ ≥ |∑ i ∈ Finset.Iic N \ {n}, (a i)| := by apply Finset.abs_sum_le_sum_abs 
    _ ≥ 0 := by apply abs_nonneg
  exact zero_lt_one
  push_neg at hn; apply lt_max_of_lt_right
  calc
    |a n| = |(a n - L) + L| := by group
    _ ≤ |a n - L| + |L| := by apply abs_add
    _ < 1 + |L| := by apply add_lt_add_of_lt_of_le (h' n hn) (le_refl |L|)
    _ = |L| + 1 := by ring


-- Prop 8.3 (a)
theorem scalar_convto (h : convto a L) {A : ℝ} : convto (fun n ↦ A * a n) (A * L) := by
  intro ε εpos
  by_cases h' : A = 0
  use 0; intro n hn
  rw[h']; simp; exact εpos
  specialize h |ε / A| (by simp; constructor; linarith; exact h')
  obtain ⟨N,hN⟩ := h
  use N; intro n hn; simp
  calc 
    |A * a n - A * L| = |A*(a n - L)| := by group
    _ = |a n - L| * |A| := by rw[mul_comm]; apply abs_mul
    _ < |ε / A| * |A| := by apply mul_lt_mul (hN n hn) (le_refl |A|); apply abs_pos.2 h'; apply abs_nonneg
    _ = ε := by rw[div_eq_mul_one_div,abs_mul, mul_assoc, ← abs_mul]; field_simp; exact le_of_lt εpos

-- Prop 8.3 (b)
theorem add_convto (ha : convto a L) (hb : convto b K) : convto (fun n ↦ a n + b n) (L + K) := by
  intro ε εpos
  obtain ⟨N,hN⟩ := ha (ε / 2) (by linarith) 
  obtain ⟨M,hM⟩ := hb (ε / 2) (by linarith)
  use max N M; intro n hn; simp
  have ngeN : n ≥ N := le_of_max_le_left hn
  have ngeM : n ≥ M := le_of_max_le_right hn
  calc 
    |a n + b n - (L + K)| = |(a n - L) + (b n - K)| := by group
    _ ≤ |a n - L| + |b n - K| := by apply abs_add
    _ < (ε / 2) + (ε / 2) := add_lt_add (hN n ngeN) (hM n ngeM)
    _ = ε := by ring

-- Prop 8.3 (c)
theorem mul_convto (ha : convto a L) (hb : convto b K) : convto (fun n ↦ a n * b n) (L * K) := by
  intro ε εpos 
  obtain ⟨M,hM⟩ := bounded_of_converges (converges_of_convto hb)
  have Mgt0 : M > 0 := lt_of_le_of_lt (abs_nonneg (b 0)) (hM 0)
  obtain ⟨N₁,hN₁⟩ := ha ((ε/2) / M) (by field_simp; exact Mgt0)
  obtain ⟨N₂,hN₂⟩ := hb ((ε/2) / (|L| + 1)) (by field_simp; apply lt_of_le_of_lt (abs_nonneg L) (by linarith))
  use max N₁ N₂; intro n hn; simp; specialize hM n
  calc
    |a n * b n - L * K| = |a n * b n + b n * L - b n * L - L * K| := by group
    _ = |b n * (a n - L) + L * (b n - K)| := by ring_nf
    _ ≤ |b n * (a n - L)| + |L * (b n - K)| := by apply abs_add
    _ = |b n| * |(a n - L)| + |L| * |(b n - K)| := by repeat rw[abs_mul]
    _ ≤ |b n| * ((ε/2) / M) + |L| * ((ε/2) /(|L| + 1)) := by 
      apply add_le_add; apply mul_le_mul (le_refl |b n|); apply le_of_lt (hN₁ n (le_of_max_le_left hn)); apply abs_nonneg; apply abs_nonneg
      apply mul_le_mul; apply le_refl; apply le_of_lt (hN₂ n (le_of_max_le_right hn)); apply abs_nonneg; apply abs_nonneg
    _ = |b n| * ((ε / 2) / M) + (ε/2) * (|L| / (|L| + 1)) := by field_simp; rw[mul_comm]
    _ ≤ |b n| * ((ε / 2) / M) + (ε / 2) * 1 := by 
      apply add_le_add; apply le_refl; apply mul_le_mul
      apply le_refl; refine (div_le_one ?_).mpr ?_; linarith[abs_nonneg L]; linarith
      apply div_nonneg (abs_nonneg L) (by linarith[abs_nonneg L]); linarith
    _ < M * ((ε / 2) / M) + (ε / 2) := by 
      apply add_lt_add_of_lt_of_le; apply mul_lt_mul (hM) (by apply le_refl); apply div_pos (by linarith) (Mgt0); exact le_of_lt Mgt0; linarith
    _ = (ε / 2) + (ε / 2) := by field_simp; ring 
    _ = ε := by ring

-- Prop 8.3 (d) 
theorem div_convto (ha : convto a L) (hb : convto b K) (bneq0 : ∀ (n : ℕ), b n ≠ 0) (Kneq0 : K ≠ 0) : 
  convto (fun n ↦ (a n / b n)) (L / K) := by

  conv =>
    lhs
    intro n; rw[div_eq_mul_one_div]
  rw[div_eq_mul_one_div]
  apply mul_convto ha
  intro ε εpos; dsimp 
  obtain ⟨N,hN⟩ := hb (|K|/2) (by field_simp)
  have aux : ∀ n ≥ N, |K| / 2 > |K| - |b n| := by 
    intro n hn; calc 
      |K| / 2 > |b n - K| := hN n hn
      _ ≥ abs (|b n| - |K|)  := abs_abs_sub_abs_le (b n) K
      _ ≥ - (|b n| - |K|) := by apply neg_le_abs
      _ = |K| - |b n| := by group
  have blarge : ∀ n ≥ N, |b n| > |K| / 2 := by
    intro n hn; apply neg_lt_neg_iff.1; apply (add_lt_add_iff_right |K|).1; 
    have : -(|K| / 2) + |K| = |K| / 2 := by ring
    conv => 
      lhs
      rw[add_comm, ← sub_eq_add_neg] 
    conv =>
      rhs 
      rw[this]
    exact aux n hn
  obtain ⟨M,hM⟩ := hb (ε*|K|^2 / 2) (div_pos (mul_pos εpos (sq_pos_of_pos (abs_pos.2 Kneq0))) zero_lt_two)
  use max N M; intro n hn; calc
    _ = |(K - b n) / (b n * K)| := by congr; field_simp [bneq0 n, Kneq0]
    _ = |K - b n| / (|b n| * |K|) := by rw[← abs_mul]; apply abs_div
    _ = |b n - K| / (|b n| * |K|) := by congr 1; exact abs_sub_comm K (b n)
    _ < (ε * |K| ^ 2 / 2) / (|b n| * |K|) := by 
      apply div_lt_div₀; apply hM n (le_of_max_le_right hn); apply le_refl
      exact le_of_lt (div_pos (mul_pos εpos (sq_pos_of_pos (abs_pos.2 Kneq0))) zero_lt_two)
      apply mul_pos <;> apply abs_pos.2; exact (bneq0 n); exact (Kneq0)
    _ ≤ (ε * |K| ^ 2 / 2) / (|K| / 2 * |K|) := by 
      apply div_le_div₀; apply mul_nonneg; apply mul_nonneg (le_of_lt εpos) (sq_nonneg |K|); linarith
      apply le_refl; apply mul_pos; apply div_pos (abs_pos.2 Kneq0) zero_lt_two; exact (abs_pos.2 Kneq0)
      apply mul_le_mul; apply le_of_lt; apply blarge n (le_of_max_le_left hn); apply le_refl; exact abs_nonneg K; exact abs_nonneg (b n)
    _ = ε := by field_simp; left; group


-- Prop 8.4
theorem cauchy_of_converges (h : converges a) : cauchy a := by 
  intro ε εpos 
  obtain ⟨L,h⟩ := h 
  obtain ⟨N,hN⟩ := h (ε/2) (by linarith)
  use N; rintro m n mgeN ngeN mgn
  calc 
    |a m - a n| = |(a m - L) + (L - a n)| := by group
    _ ≤ |a m - L| + |L - a n| := by apply abs_add
    _ = |a m - L| + |-(a n - L)| := by group 
    _ = |a m - L| + |a n - L| := by apply add_left_cancel_iff.2; apply abs_neg
    _ < (ε / 2) + (ε / 2) := add_lt_add (hN m mgeN) (hN n ngeN)
    _ = ε := by simp

-- Prop 8.5 
theorem bounded_of_cauchy (h: cauchy a) : bounded a := by
  obtain ⟨N, hN⟩ := h 1 (zero_lt_one) 
  let M := max (∑ i ≤ N, |a i| + 1) (|a N| + 1)
  have hM : M =  max (∑ i ∈ Finset.Iic N, |a i| + 1) (|a N| + 1) := rfl
  use M; intro n
  by_cases hn : n ≥ N
  specialize hN n N hn (le_refl N) hn
  calc
    |a n| = |(a n - a N) + a N| := by group
    _ ≤ |a n - a N| + |a N| := by apply abs_add
    _ < 1 + |a N| := add_lt_add_of_lt_of_le hN (le_refl |a N|)
    _ ≤ M := by rw[add_comm]; apply le_max_of_le_right; apply le_refl

  push_neg at hn
  apply lt_max_of_lt_left; rw[← add_zero |a n|]; apply add_lt_add_of_le_of_lt
  apply le_of_sub_nonneg
  have h : n ∈ Finset.Iic N := Finset.mem_Iic.mpr (le_of_lt hn)
  calc
    ∑ i ∈ Finset.Iic N, |a i| - |a n| = ∑ i ∈ Finset.Iic N \ {n}, |a i| := by
      rw [← Finset.sum_sdiff, Finset.sdiff_singleton_eq_erase]; simp; exact Finset.singleton_subset_iff.2 h
    _ ≥ |∑ i ∈ Finset.Iic N \ {n}, (a i)| := by apply Finset.abs_sum_le_sum_abs 
    _ ≥ 0 := by apply abs_nonneg
  exact zero_lt_one

-- Prop 8.7 (a)
theorem scalar_cauchy (h: cauchy a) {A : ℝ} : cauchy (fun n ↦ A * a n) := by 
  intro ε εpos
  by_cases h' : A = 0
  use 0; rintro m n m0 n0 mn
  rw[h']; simp; exact εpos
  specialize h (ε / |A|) (by apply div_pos (εpos) (abs_pos.2 h')) 
  obtain ⟨N,hN⟩ := h
  use N; rintro m n mgeN ngeN mn; simp
  calc
    |A * a m - A * a n| = |A| * |a m - a n| := by rw[← abs_mul]; group
    _ < |A| * (ε / |A|) := by apply mul_lt_mul' (le_refl |A|) (hN m n mgeN ngeN mn);  apply abs_nonneg; exact (abs_pos.2 h')  
    _ = ε := by field_simp

-- Prop 8.7 (b) 
theorem add_cauchy (ha : cauchy a) (hb : cauchy b) : cauchy (fun n ↦ a n + b n) := by
  intro ε εpos
  obtain ⟨N,hN⟩ := ha (ε / 2) (by linarith) 
  obtain ⟨M,hM⟩ := hb (ε / 2) (by linarith)
  use max N M; rintro m n hm hn mn; simp
  calc 
    |a m + b m - (a n + b n)| = |(a m - a n) + (b m - b n)| := by group
    _ ≤ |a m - a n| + |b m - b n| := by apply abs_add
    _ < (ε/2) + (ε/2) := by apply add_lt_add (hN m n (le_of_max_le_left hm) (le_of_max_le_left hn) mn) (hM m n (le_of_max_le_right hm) (le_of_max_le_right hn) mn) 
    _ = ε := by ring

-- Prop 8.7 (c)
theorem mul_cauchy (ha : cauchy a) (hb : cauchy b) : cauchy (fun n ↦ a n * b n) := by

  rintro ε εpos
  obtain ⟨L,hL⟩ := bounded_of_cauchy ha
  obtain ⟨K,hK⟩ := bounded_of_cauchy hb
  have Lpos : L > 0 := lt_of_le_of_lt (abs_nonneg (a 0)) (hL 0)
  have Kpos : K > 0 := lt_of_le_of_lt (abs_nonneg (b 0)) (hK 0)
  obtain ⟨N,hN⟩ := hb ((ε/2) / L) (by field_simp; exact Lpos)
  obtain ⟨M,hM⟩ := ha ((ε/2) / K) (by field_simp; exact Kpos)
  use max N M; rintro m n hm hn mn; simp
  calc 
    |a m * b m - a n * b n| = |a m * b m - b m * a n + b m * a n - a n * b n| := by group
    _ = |b m * (a m - a n) + a n * (b m - b n)| := by group
    _ ≤ |b m * (a m - a n)| + |a n * (b m - b n)| := by apply abs_add
    _ = |b m| * |a m - a n| + |a n| * |b m - b n| := by repeat rw[abs_mul]
    _ ≤ K * |a m - a n| + L * |b m - b n| := by
      apply add_le_add; apply mul_le_mul (le_of_lt (hK m)) (by apply le_refl); apply abs_nonneg; exact le_of_lt Kpos
      apply mul_le_mul (le_of_lt (hL n)) (by apply le_refl); apply abs_nonneg; exact le_of_lt Lpos
    _ < K * ((ε/2) / K) + L * ((ε/2) / L) := by 
      apply add_lt_add; apply mul_lt_mul' (le_refl K) (hM m n (le_of_max_le_right hm) (le_of_max_le_right hn) mn) (by apply abs_nonneg) (Kpos)
      apply mul_lt_mul' (le_refl L) (hN m n (le_of_max_le_left hm) (le_of_max_le_left hn) mn) (by apply abs_nonneg) (Lpos)
    _ = (ε / 2) + (ε / 2) := by field_simp; ring
    _ = ε := by ring

-- Prop 8.7 (d)
theorem div_cauchy (hb : cauchy b) (bpos : ∃ (δ : ℝ), δ > 0 ∧ ∀ (n : ℕ), |b n| ≥ δ) : 
cauchy (fun n ↦ 1 / b n) := by 

  intro ε εpos 
  obtain ⟨δ,δpos,h⟩ := bpos
  obtain ⟨N,hN⟩ := hb (ε*(δ^2)) (mul_pos εpos (by field_simp))
  use N; rintro m n hm hn mn; dsimp
  have bound : ∀ (n : ℕ), 1 / |b n| ≤ 1 / δ := by intro k; apply div_le_div₀ (zero_le_one) (le_refl 1) δpos (h k)
  have neq0 : ∀ (n : ℕ), b n ≠ 0 := by 
    intro k; apply abs_pos.1; calc
      |b k| ≥ δ := h k
      _ > 0 := δpos

  calc 
    |1 / b m - 1 / b n| = |(b n - b m) / (b m * b n)| := by 
      congr; rw[← div_sub_div_same, div_mul_cancel_right₀,div_mul_cancel_left₀]; simp; exact (neq0 m); exact (neq0 n)
    _ = |1 / (b m * b n)| * |b n - b m| := by rw[div_eq_mul_one_div, abs_mul,mul_comm]
    _ = (1 / |b m|) * (1 / |b n|) * |b n - b m| := by rw[abs_div, abs_one, abs_mul]; ring
    _ ≤ (1 / δ) * (1 / δ) * |b n - b m| := by 
      apply mul_le_mul; apply mul_le_mul (bound m) (bound n); apply div_nonneg (zero_le_one) (abs_nonneg (b n))
      apply div_nonneg (zero_le_one) (le_of_lt δpos); apply le_refl; apply abs_nonneg; apply mul_nonneg <;> exact div_nonneg (zero_le_one) (le_of_lt δpos)
    _ = (1 / δ^2) * |-(b n - b m)| := by rw[abs_neg]; ring
    _ = (1 / δ^2) * |b m - b n| := by simp
    _ < (1 / δ^2) * (ε * δ ^ 2) := by apply mul_lt_mul'; apply le_refl; exact hN m n hm hn mn; apply abs_nonneg; exact div_pos zero_lt_one (sq_pos_of_pos δpos)
    _ = ε := by field_simp

end Theorems


-- CHAPTER 9 : A Closer Look at the Real Number System

section  Definitions

-- Def 9.1

def bounded_set (S : Set ℝ) := 
  ∃ (M : ℝ), ∀ n : ℝ, n ∈ S → |n| < M

def bounded_above (S : Set ℝ) :=
  ∃ (y : ℝ), ∀ (x : ℝ), x ∈ S → x ≤ y 

def UpBound (S : Set ℝ) (y : ℝ) :=
  ∀ (x : ℝ), x ∈ S → x ≤ y

def bounded_below (S : Set ℝ) :=
  ∃ (y : ℝ), ∀ (x : ℝ), x ∈ S → y ≤ x

def LowBound (S : Set ℝ) (y : ℝ) :=
  ∀ (x : ℝ), x ∈ S → y ≤ x


-- Def 9.2 
def sup (S : Set ℝ) (y : ℝ) :=
  UpBound S y ∧ ( ∀ (z : ℝ), UpBound S z → y ≤ z )

def inf (S : Set ℝ) (y : ℝ) :=
  LowBound S y ∧ ( ∀ (z : ℝ), LowBound S z → z ≤ y )

def fsup (a : ℕ → ℝ) (y : ℝ) := 
  sup (a '' {n | n : ℕ}) y

def finf (a : ℕ → ℝ) (y : ℝ) :=
  inf (a '' {n | n : ℕ}) y


def mono_inc (a : ℕ → ℝ) :=
  ∀ {m n : ℕ}, m ≤ n → a m ≤ a n

def mono_dec (a : ℕ → ℝ) :=
  ∀ {m n : ℕ}, m ≤ n → a n ≤ a m

end Definitions 

section  Theorems 
variable {a b : ℕ → ℝ}
variable {L K x y : ℝ}
variable {S : Set ℝ}


lemma mono_inc_of_inc (h : ∀ n, a n ≤ a (n+1)) : mono_inc a := by 
  intro m n mln
  induction mln with 
  | refl => exact le_refl (a m)
  | step hk ih =>
    apply le_trans ih
    apply h

lemma mono_dec_of_dec (h : ∀ n, a (n+1) ≤ a n) : mono_dec a := by
  intro m n mln
  induction mln with 
  | refl => exact le_refl (a m)
  | step hk ih =>
    apply ge_trans ih
    apply h


-- Completeness Axiom
theorem converges_of_cauchy (h : cauchy a) : converges a := sorry

theorem exists_sup (h : bounded_above S) (nonempty : ∃ x, x ∈ S) : ∃ y, sup S y := sorry

theorem exists_inf (h : bounded_below S) (nonempty : ∃ x, x ∈ S) : ∃ y, inf S y := sorry


-- Lemma 9.1
lemma convto_nonneg (ha : convto a L) (h : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → a n ≥ 0) : L ≥ 0 := by 
  by_contra! Lneg 
  obtain ⟨N,h⟩  := h
  obtain ⟨M,hM⟩ := ha (|L|/2) (by apply div_pos (abs_pos_of_neg Lneg) (zero_lt_two))
  let n := max N M 
  have hn : n = max N M := rfl
  have bins : a n - L < |L| / 2 := lt_of_abs_lt (hM n (le_max_right N M))
  have oops : (0 : ℝ) < 0 := by 
    calc
      0 ≤ a n := h n (le_max_left N M)
      _ = (a n - L) + L := by group
      _ < |L| / 2 + L := by apply add_lt_add_right bins
      _ = - L / 2 + L := by congr; exact abs_eq_neg_self.2 (le_of_lt Lneg)
      _ = L / 2 := by ring
      _ < 0 := by rw[div_eq_mul_one_div]; apply mul_neg_of_neg_of_pos (Lneg) (by linarith)
  linarith

-- Lemma 9.2
lemma le_convto_of_le (ha : convto a L) (hb : convto b K) (h : ∃ (N : ℕ), ∀ n ≥ N, a n ≤ b n) : L ≤ K := by
  let c n := b n + -1 * a n
  
  have hc : convto c (K - L) := by 
    apply add_convto hb; rw[neg_eq_neg_one_mul L]; apply scalar_convto ha
  
  obtain ⟨N,hN⟩ := h
  have h' : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → 0 ≤ c n := by 
    use N; intro n hn; specialize hN n hn; simp [c]; exact hN
  
  apply le_of_sub_nonneg
  exact convto_nonneg hc h'


-- Thm 9.2 (a)
theorem converges_of_mono_inc_of_bounded (ma : mono_inc a) (ba : bounded a) : converges a := by
  let A := a '' {n : ℕ | true}  
  have h : A = a '' {n : ℕ | true}  := rfl
  obtain ⟨M,hM⟩ := ba
  have bA : bounded_above A := by 
    conv => 
      rhs; rw[h]
    use M; intro x xa
    obtain ⟨y,⟨hy,ay⟩⟩ := xa
    rw[← ay]; exact le_of_lt (lt_of_abs_lt (hM y))

  obtain ⟨y,⟨By,hy⟩⟩ := exists_sup bA (by use a 0; exact Set.mem_image_of_mem a rfl)
  use y; intro ε εpos
  have guy : ∃ z ∈ A, y - ε < z := by
    by_contra! guys 
    have yUps : UpBound A (y - ε) := guys
    specialize hy (y - ε) yUps
    linarith
  rw[h] at guy
  obtain ⟨z,⟨w,⟨hw,awz⟩⟩,yltz⟩ := guy
  use w; intro n ngew
  have angaw : a n ≥ a w := ma ngew 
  calc
    _ = - (a n - y) := by 
      apply abs_eq_neg_self.2; apply sub_nonpos.2;
      specialize By (a n) (by rw[h]; simp); exact By
    _ = y - a n := by ring
    _ ≤ y - a w := sub_le_sub (le_refl y) (angaw)
    _ < y - (y - ε) := by rw[awz]; apply sub_lt_sub_left (yltz)
    _ = ε := by ring
    
--Thm 9.2 (b) 
theorem converges_of_mono_dec_of_bounded (ma : mono_dec a) (ba : bounded a) : converges a := by 
  let b n := -1 * a n
  have : ∀ n, b n = - a n := by intro n; exact neg_one_mul (a n)
  have mb : mono_inc b := by 
    intro m n mlen
    specialize ma mlen 
    rw[this,this]; linarith
  have bb : bounded b := by
    obtain ⟨M,hM⟩ := ba
    use M; intro n; rw[this n, abs_neg]; exact hM n
  have cb : converges b := converges_of_mono_inc_of_bounded mb bb
  obtain ⟨K,h⟩ := cb
  use -1 * K 
  have aa : a = fun n ↦ -1 * b n := by funext n; rw[this n]; simp
  rw[aa]; exact scalar_convto h


-- Prop 9.6 
theorem archify (x : ℝ) (h: x > 0) : ∃ (N : ℕ), N > 0 ∧ 1 / N < x := by 
  use Nat.ceil (1 / x) 
  sorry

-- theorem squeeze_thm (ha : convto a L) (hb : convto b L) (h : ∃ N, ∀ N) 

end Theorems


-- CHAPTER 10 : Series, Part 1

section  Definitions

-- Def 10.1
def series (a : ℕ → ℝ) := 
  fun n ↦ ∑ i ∈ Finset.range (n+1), a i

def series' (a : ℕ → ℝ) : (ℕ → ℝ) 
  | 0 => a 0 
  | n + 1 => series a n + a (n+1) 

def a0 : ℕ → ℝ  
  | 0 => 0
  | n+1 => n+1

def a (n : ℕ) :=
  2*n

#eval a0 6

#eval series' a0 6

-- Def 10.2
def geo_series (a₀ r : ℝ) := 
  series (fun n ↦ a₀ * r ^ n)

noncomputable def p_series (p : ℝ) :=
  series (fun n ↦ 1 / (n + 1) ^ p )

-- Def 10.3
def conv_absolutely (a : ℕ → ℝ) := 
  converges (series (fun n ↦ |a n|))

def conv_conditionally (a : ℕ → ℝ) := 
  converges (series a) ∧ ¬conv_absolutely a

end Definitions

section  Theorems 

variable {a b : ℕ → ℝ}
variable {L K r a₀ : ℝ}
variable {n : ℕ}

theorem series_eq : series = series' := by 
  symm
  unfold series series'
  ext a x; induction' x with n h
  simp
  simp; by_cases h': n = 0
  rw[h']; rw[h'] at h
  have h'' : series a 0 = ∑ i ∈ Finset.range (1), a i := rfl
  rw[h'']; simp_all; symm; calc
    _ = ∑ i ∈ {0,1}, a i := rfl
    _ = ∑ i ∈ {0}, a i + ∑ i ∈ {1}, a i := Eq.symm (Real.ext_cauchy
          (congrArg Real.cauchy (congrFun (congrArg HAdd.hAdd h'') (∑ i ∈ {1}, a i))))
    _ = a 0 + a 1 := by congr; exact Finset.sum_singleton a 1
  have h'' : ∃ y : ℕ, n = y.succ := Nat.exists_eq_succ_of_ne_zero h'
  obtain ⟨y,hy⟩ := h''
  simp_all; symm; calc
    _ = (∑ x ∈ Finset.range (y + 1 + 1), a x) + a (y + 1 + 1) := Finset.sum_range_succ a (y + 2)
    _ = series a y + a (y+1) + a (y + 1 + 1) := by rw[← h]
    _ = series a (y + 1) + a (y + 1 + 1) := by congr

lemma sequence_to_series {a : ℕ → ℝ} {n : ℕ} (h: n ≠ 0) : a n = series a n - series a (n-1) := by
  unfold series
  have : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero h
  symm; calc
    _ = ∑ i ∈ Finset.range (n), a i + a n - ∑ i ∈ Finset.range (n - 1 + 1), a i := by congr; exact Finset.sum_range_succ a n
    _ = ∑ i ∈ Finset.range (n), a i + a n - ∑ i ∈ Finset.range (n), a i := by 
      symm; conv => rhs; rhs; lhs; rhs; rw[this]
    _ = a n := by simp

lemma sequence_to_series' {a : ℕ → ℝ} {n : ℕ} (h: n ≠ 0) : a n = series' a n - series' a (n-1) := by 
  rw[← series_eq]; exact sequence_to_series h 


lemma series'_zero : series' a 0 = a 0 := by
  unfold series'; simp

lemma series_zero : series a 0 = a 0 := by 
  rw[series_eq]; exact series'_zero


lemma series_succ : series a (n+1) = series a n + a (n+1) := by 
  rw[@sequence_to_series a (n+1) (by linarith)]; simp

lemma series'_succ : series' a (n+1) = series' a n + a (n+1) := by 
  rw[@sequence_to_series' a (n+1) (by linarith)]; simp


lemma mono_inc_of_nonneg (h : ∀ n, a n ≥ 0) : mono_inc (series a) := by 
  apply mono_inc_of_inc; rw[series_eq]; intro n; 
  have : series' a (n+1) = series' a n + a (n+1) := by 
    rw[@sequence_to_series' a (n+1) (by linarith)]; simp
  rw[this]; simp; exact h (n+1)

lemma mono_dec_of_nonpos (h : ∀ n, a n ≤ 0) : mono_dec (series a) := by 
  apply mono_dec_of_dec; intro n
  calc 
    _ = series a n + a (n+1) := by rw[@sequence_to_series a (n+1) (by linarith)]; simp
    _ ≤ series a n := by simp; exact h (n+1)

-- Prop 10.1
theorem nth_term_test (h : converges (series a)) : convto a 0 := by 
  intro ε εpos; simp
  obtain ⟨L,h⟩ := h
  rw[series_eq] at h
  obtain ⟨N,hN⟩ := h (ε/2) (by linarith)
  use N + 1; intro n hn 
  have ne0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  calc 
  _ = |series' a n - series' a (n-1)| := by rw [← sequence_to_series' ne0]
  _ = |(series' a n - L) - (series' a (n-1) - L)| := by simp
  _ ≤ |series' a n - L| + |series' a (n-1) - L| := by apply abs_sub
  _ < (ε / 2) + (ε / 2) := by apply add_lt_add (hN n (by linarith)) (hN (n-1) (Nat.le_sub_one_of_lt hn))
  _ = ε := by group


--Prop 10.1 (a)
theorem scalar_series (ha : convto (series a) L) {A : ℝ} : convto (series (fun n ↦ A * a n)) (A * L) := by
  have : series (fun n ↦ A * a n) = fun n ↦ A * series a n := by
    funext n; unfold series; simp; rw[Finset.mul_sum]
  conv => lhs; rw[this]
  exact scalar_convto ha
  

-- Prop 10.2 (b)
theorem add_series (ha : convto (series a) L) (hb : convto (series b) K) : 
convto (series (fun n ↦ a n + b n)) (L + K) := by 
  have : series (fun n ↦ a n + b n) = fun n ↦ (series a n + series b n) := by
    funext n; unfold series; simp; rw[Finset.sum_add_distrib]
  conv => lhs; rw[this]
  exact add_convto ha hb

--Prop 10.3 (a)

lemma harmonic_sq_conv: convto (fun n ↦ 1 / n) 0 := by 
  intro ε εpos
  obtain ⟨N, ⟨Npos, hN⟩⟩ := archify ε εpos
  use max N 1; intro n hn; dsimp; rw[sub_zero]
  have : 1 / (↑n) ≥ 0 := by exact Nat.zero_le (1 / n)
  rw[ abs_eq_self.2]; refine (one_div_lt εpos ?_).mp ?_; 
  have xx : n ≥ 1 := le_of_max_le_right hn

  calc
    (0 : ℝ) < 1 := zero_lt_one
    1 ≤ ↑n := by exact Nat.one_le_cast.mpr xx

  have hNN : 1 / ε < ↑N := by 
    apply lt_of_one_div_lt_one_div; exact Nat.cast_pos'.mpr Npos; rw[one_div_div,div_one]; exact hN 
  
  have why : ↑N ≤ n := le_of_max_le_left hn

  have step1 : 1 / ε < ↑N := hNN
  have step2 : ↑N ≤ ↑n := Nat.cast_le.mpr (le_of_max_le_left hn)
  apply lt_of_lt_of_le step1; exact Nat.cast_le.mpr why
  exact Nat.one_div_cast_nonneg n

theorem geo_converges (h : |r| < 1) : convto (geo_series a₀ r) (a₀ / (1 - r)) := by 

  have rn1 : 1 - r ≠ 0 := by apply lt_of_abs_lt at h; linarith
  have : series (fun n ↦ a₀ * r ^ n) = fun n ↦ (a₀ * series (fun n ↦ r^n) n) := by 
    funext n; unfold series; simp; exact Eq.symm (Finset.mul_sum (Finset.range (n + 1)) (HPow.hPow r) a₀)
  conv => lhs; unfold geo_series; simp; 
  apply scalar_series;  
  have h'' : (series (HPow.hPow r)) = fun n ↦ ((1 - r^(n+1)) / (1-r)) := by 
    funext n; induction' n with n hn 
    rw[series_zero]; simp; rw[div_self]; intro a; apply rn1; linarith
    rw[series_succ, hn]
    calc
      _ =  (1 - r ^ (n + 1)) / (1 - r) + (1-r)* r ^ (n + 1) / (1-r) := by 
        apply add_left_cancel_iff.2; rw[mul_comm, div_eq_mul_one_div]
        exact mul_mul_div (r ^ (n + 1)) rn1
      _ = (1 - r ^ (n + 1) + (1-r)* r ^ (n + 1)) / (1 - r) := 
        div_add_div_same (1 - r ^ (n + 1)) ((1 - r) * r ^ (n + 1)) (1 - r)
      _ = (1 - r ^ (n + 1) + (r ^ (n + 1) - r * r ^ (n + 1))) / (1 - r) := by 
        conv => lhs; lhs; rw[mul_sub_right_distrib, one_mul]
      _ = (1 - r * r ^ (n + 1)) / (1 - r) := by rw[sub_add_sub_cancel]
      _ = (1 - r ^ (1) * r ^ (n + 1)) / (1 - r) := by rw [npow_one]
      _ = (1 - r ^ (n + 1 + 1)) / (1 - r) := by rw[← pow_add]; ring

  rw[h'', inv_eq_one_div]; apply div_convto
  nth_rw 3 [← add_zero 1]; apply add_convto convto_constant

  intro ε εpos; simp

  by_cases hr : |r| = 0
  rw[hr]; simp; use 0; intros; exact εpos
 
  have agr : |r| > 0 := lt_of_le_of_ne (abs_nonneg r) (by symm; exact hr)

  have xr : ∃ x > 0, |r| = 1 / (1+x) := by
    use (1 / |r|) - 1; constructor
    apply sub_lt_iff_lt_add.1; rw[sub_neg_eq_add, zero_add]
    exact (one_lt_div agr).2 h; simp

  obtain ⟨x,xpos,hx⟩ := xr

  have aux : ∀ n : ℕ, (1 + x) ^ n ≥ 1 + x*n := by 
    intro n; induction' n with n hn

    simp; calc
      (1 + x) ^ (n + 1) = (1 + x) ^ n * (1 + x) := rfl
      _ ≥ (1 + x * ↑n) * (1 + x) := by 
        apply mul_le_mul hn (le_refl (1 + x)); linarith
        apply pow_nonneg (by linarith)
      _ = (1 + x * ↑n) + x * (1 + x * ↑n) := by rw [left_distrib]; simp; rw[mul_comm]
      _ = (1 + x * ↑n + x) + (x * x * ↑n) := by 
        rw[left_distrib]; simp; ring
      _ ≥ (1 + x * ↑n + x) + 0 := by 
        apply add_le_add; apply le_refl; apply mul_nonneg (mul_nonneg (le_of_lt xpos) (le_of_lt xpos))
        exact Nat.cast_nonneg' n
      _ = 1 + x * ↑n + x := by rw[add_zero]
      _ = 1 + x * (↑n + 1) := by rw [mul_add_one]; ring 
      _ = _ := by norm_cast

  have windup : ∀ n : ℕ , n > 0 → |r| ^ n ≤ 1 / (n*x) := by 
    intro n npos; calc
      _ = 1 / (1 + x) ^ n := by rw[hx]; simp
      _ ≤ 1 / (1 + n*x) := by 
        apply div_le_div₀ zero_le_one (le_refl 1); apply add_pos zero_lt_one; apply mul_pos; 
        exact Nat.cast_pos'.mpr npos; exact xpos; rw[mul_comm]; exact aux n

      _ ≤ _ := by 
        apply div_le_div₀ zero_le_one (le_refl 1); exact mul_pos (Nat.cast_pos'.mpr npos) xpos
        nth_rw 1 [← zero_add (↑n * x)]; exact add_le_add zero_le_one (le_refl (↑n * x))

  have cc : convto (fun n ↦ 1 / (n*x)) 0 := by 
    have fo : (fun n : ℕ ↦ 1 / (n * x : ℝ)) = (fun n ↦ (1 / x) * (1 / (n : ℕ))) := by
      funext n; simp
    rw [fo]
    have gg : (1 / x) * 0 = 0 := by simp
    rw[← gg]
    apply scalar_convto 
    exact harmonic_sq_conv
    
  obtain ⟨N,hN⟩ := cc ε εpos
  use N+1; intro n hn
  have npos : n > 0 := Nat.zero_lt_of_lt hn
  specialize hN n (by linarith); dsimp at hN; rw[sub_zero] at hN
  calc 
    _ = |r| * |r| ^ n := pow_succ' |r| n
    _ ≤ 1 * |r| ^ n := by 
      apply mul_le_mul (le_of_lt h); apply le_refl; apply pow_nonneg
      exact (abs_nonneg r); exact zero_le_one 
    _ = |r| ^ n := by rw[one_mul]
    _ ≤ 1 / (↑n * x) := windup n npos
    _ < ε := by apply lt_of_abs_lt hN
  apply convto_constant
  intro; exact rn1
  exact rn1

--Prop 10.3 (b)
theorem geo_diverges (h : |r| ≥ 1) (an0 : a₀ ≠ 0 ) : ¬ converges (geo_series a₀ r) := by 
  intro cg 
  have : ∀ n, (series (fun n ↦ a₀ * r ^ n) n) = a₀ * (series fun n ↦ r ^ n) n := by 
    intro n; unfold series; simp; exact Eq.symm (Finset.mul_sum (Finset.range (n + 1)) (HPow.hPow r) a₀)

  obtain cauch := cauchy_of_converges cg 
  contrapose! cauch; unfold cauchy; push_neg
  use |a₀|; constructor; exact abs_pos.2 an0
  intro N; use N+1, N 
  constructor; linarith
  constructor; linarith
  constructor; linarith
  unfold geo_series; rw[series_succ]; simp
  rw[abs_mul]; nth_rw 1 [← mul_one |a₀|]
  apply mul_le_mul; apply le_refl
  rw[abs_pow]; exact one_le_pow₀ h
  exact zero_le_one; apply abs_nonneg

lemma general_geo_test (h : |r| < 1) : converges (series (fun n ↦ a₀ * r ^ n)) := by 
  apply converges_of_convto; apply geo_converges h



--Prop 10.4
theorem conv_of_conv_absolutely (h : conv_absolutely a) : converges (series a) := by 
  apply converges_of_cauchy 
  have cabs : cauchy (series (fun n ↦ |a n|)) := cauchy_of_converges h
  intro ε εpos
  obtain ⟨N,hN⟩ := cabs ε εpos 
  use N; intro m n xx w y
  specialize hN m n xx w y; unfold series; unfold series at hN; simp at hN
  calc 
    _ = |∑ i ∈ Finset.range (m+1) \ Finset.range (n+1) , a i| := by 
      congr; apply Eq.symm (Finset.sum_sdiff_eq_sub _); exact Finset.range_subset.mpr (by linarith)
    _ ≤ ∑ i ∈ Finset.range (m+1) \ Finset.range (n+1) , |a i| := by apply Finset.abs_sum_le_sum_abs
    _ = ∑ i ∈ Finset.range (m+1), |a i| - ∑ i ∈ Finset.range (n+1) , |a i| := by
      apply Finset.sum_sdiff_eq_sub; exact Finset.range_subset.mpr (by linarith)
    _ < ε := lt_of_abs_lt hN

--Prop 10.5
theorem comparison_test (b) (anneg : ∀ n, a n ≥ 0) (aleb : ∀ n, a n ≤ b n) (cb : converges (series b)) : 
converges (series a) := by

  have bb : bounded (series b) := bounded_of_converges cb
  obtain ⟨L,hL⟩ := bb 

  have ba : bounded (series a) := by 
    use L ; intro n; calc
      _ = series a n := by 
        apply abs_eq_self.2; induction' n with n hn
        rw[series_eq]; unfold series'; dsimp; exact anneg 0
        rw[series_succ]; apply add_nonneg hn (anneg (n+1))
      _ ≤ series b n := by 
        induction' n with n hn 
        rw[series_zero,series_zero]; exact aleb 0 
        rw[series_succ,series_succ]; exact add_le_add hn (aleb (n+1))
      _ < L := lt_of_abs_lt (hL n)

  have ma : mono_inc (series a) := mono_inc_of_nonneg anneg 
  exact converges_of_mono_inc_of_bounded ma ba

lemma general_comparison_test (b) (N : ℕ) (anneg : ∀ n, a n ≥ 0) (aleb : ∀ n ≥ N, a n ≤ b n) (cb : converges (series b)) : 
converges (series a) := by 
  -- have bb : bounded (series b) := bounded_of_converges cb
  -- obtain ⟨L,hL⟩ := bb 

  -- -- have bnng: ∀ n, b n ≥ 0 := by 

  -- have ba : bounded (series a) := by 
  --   use max L (∑ i ∈ Finset.range (N + 1), |a i|)
  --   intro n; calc
  --     _ = series a n := by 
  --       apply abs_eq_self.2; induction' n with n hn
  --       rw[series_eq]; unfold series'; dsimp; exact anneg 0
  --       rw[series_succ]; apply add_nonneg hn (anneg (n+1))
  --     _ ≤ max (series b n)  (∑ i ∈ Finset.range (N + 1), |a i|) := by 
  --       induction' n with n hn 
  --       rw[series_zero,series_zero]; apply le_max_of_le_right; trans |a 0|; apply le_abs_self
  --       trans ∑ i ∈ Finset.range (N + 1) \ {0}, |a i| + |a 0|
  --       nth_rw 1[← zero_add |a 0|]; apply add_le_add; trans |∑ i ∈ Finset.range (N + 1) \ {0}, a i|
  --       apply abs_nonneg; apply Finset.abs_sum_le_sum_abs; apply le_refl
  --       apply le_of_eq; refine Eq.symm (Finset.sum_eq_sum_diff_singleton_add ?_ fun x ↦ |a x|); refine
  --         Finset.mem_range_succ_iff.mpr ?_ ; exact Nat.zero_le N
  --       apply le_max_of_le_left
  --       rw[series_succ, series_succ]
  --       apply add_le_add; apply?

  --     _ = 

  --     _ < L + ∑ i ∈ Finset.range (N + 1), |a i| := by apply add_lt_add_of_lt_of_le (lt_of_abs_lt (hL n)); apply le_refl

  -- have ma : mono_inc (series a) := mono_inc_of_nonneg anneg 
  -- exact converges_of_mono_inc_of_bounded ma ba
  sorry

--Thm 10.1

lemma b_geo_p_series {n : ℕ} (h : )

theorem p_series_test {p : ℝ} : converges (p_series p) ↔ p > 1 := by 
  constructor; intro h; 
  obtain ⟨M, hM⟩ := bounded_of_converges h
  unfold boundedby p_series at hM
  contrapose! hM with pl1 


--Thm 10.2
theorem ratio_test_conv  (L : ℝ) (Llt1 : L < 1) (h : convto (fun n ↦ |a (n + 1) / a n|) L) (h' : ∀ n, a n ≠ 0) : conv_absolutely a := by 

  have Lnn : L ≥ 0 := by apply convto_nonneg at h; apply h; use 0; intros; apply abs_nonneg
  have eguy : ∃ ε > 0, L + ε < 1 := by  
    use (1 - L) / 2; constructor; apply div_pos (by linarith) zero_lt_two; linarith
  obtain ⟨ε,εpos,eguy⟩ := eguy
  obtain ⟨N, hN⟩ := h ε εpos

  have aux : ∀ n ≥ N, |a (n+1)| < |a n| * (L + ε) := by 
    intro n hn; specialize hN n hn; simp at hN
    apply lt_of_abs_lt at hN; rw[abs_div] at hN
    apply sub_lt_iff_lt_add.1 at hN
    have : |a n| > 0 := abs_pos.2 (h' n)
    calc 
      _ = |a (n + 1)| / |a n| * |a n| := by rw[div_mul_cancel_of_imp]; intro; linarith
      _ < |a n| * (L + ε) := by 
        rw[mul_comm]; apply mul_lt_mul' (le_refl |a n|); rw[add_comm L]; exact hN; 
        apply div_nonneg <;> apply abs_nonneg; exact this

  have auxer : ∀ n ≥ N, |a (n+1)| < |a N| * (L + ε)^(n - N) := by
    intro n hn
    induction' n with n ih
    have n0 : N = 0 := Nat.eq_zero_of_le_zero hn
    rw[n0]; simp
    specialize aux 0 hn; simp at aux
    trans |a 0| * (L + ε); exact aux
    nth_rw 2 [← mul_one |a 0|]; apply mul_lt_mul' (le_refl |a 0|) eguy (by linarith) (abs_pos.2 (h' 0))
    by_cases gethim : n + 1 = N
    rw[gethim]; simp
    trans |a N| * (L + ε)
    exact aux N (le_refl N)
    nth_rw 2 [← mul_one |a N|]; apply mul_lt_mul' (le_refl |a N|) eguy (by linarith) (abs_pos.2 (h' N))
    have trippin : n+1 > N :=  Nat.lt_of_le_of_ne hn fun a ↦ gethim (id (Eq.symm a))
    have stumblin : n ≥ N := Nat.le_of_lt_succ trippin 
    specialize ih stumblin 
    have fallin : n - N + 1 = n + 1 - N := by exact Eq.symm (Nat.sub_add_comm stumblin)
    calc 
      _ < |a (n + 1)| * (L + ε) := aux (n+1) (by linarith)
      _ < |a N| * (L + ε) ^ (n - N) * (L + ε) := by 
        apply mul_lt_mul ih (le_refl (L + ε)) (by linarith)
        apply mul_nonneg (abs_nonneg (a N)); apply pow_nonneg (by linarith)
      _ = |a N| * (L + ε) ^ (n - N + 1) := by ring
      _ = _ := by rw[fallin]

  have junv {n : ℕ}: n - 1 - N = n - (N + 1) := by rw [Nat.Simproc.sub_add_eq_comm]

  
  unfold conv_absolutely 
  apply general_comparison_test (fun n ↦ |a N| * (L + ε) ^ (n - 1 - N)) (max (N+1) 1) 
  intro; apply abs_nonneg
  intro n hn
  have gigi : n ≥ N + 1 := le_of_max_le_left hn
  have gugu : n ≥ 1 := le_of_max_le_right hn
  have ngN : n ≥ N := Nat.le_of_succ_le gigi
  have : n - 1 ≥ N := (Nat.le_sub_one_iff_lt gugu).mpr gigi
  
  specialize auxer (n-1) this; simp at auxer; 
  calc
    _ = |a (n - 1 + 1)| := by congr; exact (Nat.sub_eq_iff_eq_add gugu).mp rfl
    _ ≤ |a N| * (L + ε) ^ (n - 1 - N) := le_of_lt auxer

  apply general_comparison_test (fun n ↦ (|a N| / ((L + ε) ^ (N + 1)) * ((L + ε)^n))) (N + 1)
  intro n
  apply mul_nonneg; apply abs_nonneg
  apply pow_nonneg; linarith
  intro n ngN
  apply le_of_eq
  calc
    _ =  |a N| * (L + ε) ^ (n - (N + 1)) := by congr 2; exact junv
    _ = |a N| * ((L+ ε) ^ n / (L + ε) ^ (N + 1)) := by 
      congr 1;   rw [← Nat.sub_add_cancel ngN]
      rw [pow_add]
      field_simp 
    _ = _ := Eq.symm (mul_comm_div |a N| ((L + ε) ^ (N + 1)) ((L + ε) ^ n))


  apply general_geo_test 
  apply abs_lt.2; constructor; linarith; exact eguy
  

theorem ratio_test_div (L : ℝ) (Lgt1 : L > 1) (h : convto (fun n ↦ |a (n + 1) / a n|) L) (h' : ∀ n, a n ≠ 0) : ¬ converges (series a) := by 
  by_contra ba 
  apply nth_term_test at ba
  contrapose! ba; unfold convto; push_neg
  clear ba
  have eguy : ∃ ε > 0, L - ε > 1 := by  
    use (L - 1) / 2; constructor; apply div_pos (by linarith) zero_lt_two; linarith
  obtain ⟨ε,⟨εpos,eguy⟩⟩ := eguy
  obtain ⟨N,hN⟩ := h ε εpos
  dsimp at hN
  use |a N|; constructor; simp; exact h' N
  intro k 
  use max N k; constructor
  exact le_max_right N k
  simp
  by_cases Nkay : N > k 
  rw[max_eq_left (le_of_lt Nkay)] 
  push_neg at Nkay
  rw[max_eq_right Nkay]

  have dimple : ∀ n ≥ N, |a (n + 1)| / |a n| > L - ε := by 
    intro n hn
    specialize hN n hn
    have : |a (n + 1) / a n| - L > - ε := neg_lt_of_abs_lt hN
    rw[← abs_div]; exact sub_lt_of_abs_sub_lt_left hN

  have simple : ∀ n ≥ N, |a (n + 1)| > |a n| := by 
    intro n hn
    specialize dimple n hn
    have : |a (n + 1)| / |a n| > 1 := gt_trans dimple eguy
    have pos : |a n| > 0 := abs_pos.mpr (h' n)
    exact (one_lt_div pos).mp this

  induction' Nkay with m h'' h'''
  exact le_refl |a N|
  simp_all 
  trans |a m|; exact h'''
  exact le_of_lt (simple m h'')


--Thm 10.3
theorem root_test_conv (h : convto (fun n ↦ |a n| ^ ((1:ℝ) / n)) L) (Llt1 : L < 1) : conv_absolutely a := by 
  have Lnn : L ≥ 0 := by apply convto_nonneg at h; apply h; use 0; intro n nng; apply Real.rpow_nonneg (abs_nonneg (a n))
  have eguy : ∃ ε > 0, L + ε < 1 := by use (1 - L) / 2; constructor; apply div_pos (by linarith) zero_lt_two; linarith
  obtain ⟨ε,εpos,eguy⟩ := eguy
  obtain ⟨N, hN⟩ := h ε εpos
  dsimp at hN
  unfold conv_absolutely
  apply general_comparison_test (fun n ↦ (L + ε) ^ (Nat.cast n : ℝ)) (N + 1) (by intro n; apply abs_nonneg)
  intro n ngN
  specialize hN n (by linarith)
  apply le_of_lt
  apply abs_lt.1 at hN
  have habben : |a n| ^ ((1:ℝ) / n) < L + ε := by apply lt_add_of_sub_left_lt; exact hN.2
  have npos : n ≠ 0 := Nat.ne_zero_of_lt ngN
  have : ((1 : ℝ) / n) * (n : ℝ) = 1 := by refine one_div_mul_cancel ?_; exact Nat.cast_ne_zero.mpr npos

  calc 
    _ = (|a n| ^ (((1 : ℝ) / n))) ^ (n : ℝ) := by nth_rw 1 [← pow_one |a n|]; symm; rw[← Real.rpow_mul (by apply abs_nonneg), this]; rw [Real.rpow_one, npow_one]
    _ < _ := by 
      apply Real.rpow_lt_rpow; apply Real.rpow_nonneg (abs_nonneg (a n)); exact habben
      have boyifi : (n : ℝ) ≥ 0 := by exact Nat.cast_nonneg' n
      have bb : (n : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr npos
      apply lt_of_le_of_ne boyifi; symm; exact bb
  
  have : (fun n ↦ (L + ε) ^ (Nat.cast n : ℝ)) = fun n ↦ 1 * (L + ε) ^ n := by 
    funext n; rw [Real.rpow_natCast]; simp

  conv => rhs; rhs; rw[this]
  apply general_geo_test
  apply abs_lt.2
  exact ⟨(by linarith),(by linarith)⟩
  

theorem root_test_div (h : convto (fun n ↦ |a n| ^ (1 / n)) L) (Lgt1 : L > 1) : ¬ converges (series a) := by 
  sorry

end Theorems


-- CHAPTER 11 : The Structure of the Real Line

section Definitions

def Ioo (a : ℝ) (b : ℝ) := 
  {x : ℝ | a < x ∧ x < b}

def Ioc (a : ℝ) (b : ℝ) :=
  {x : ℝ | a < x ∧ x ≤ b}

def Ico (a : ℝ) (b : ℝ) :=
  {x : ℝ | a ≤ x ∧ x < b}

def Icc (a : ℝ) (b : ℝ) :=
  {x : ℝ | a ≤ x ∧ x ≤ b}

def c (U : Set ℝ) :=
  {x : ℝ | x ∉ U}

def in_set (a : ℕ → ℝ) (D : Set ℝ) :=
  ∀ n, a n ∈ D

-- Def 11.1
def Open (U : Set ℝ) := 
  ∀ x ∈ U, ∃ ε > 0, (Ioo (x - ε) (x + ε)) ⊆ U 

--Def 11.2
def Closed (E : Set ℝ) :=
  Open (c E)

--Def 11.3
def acc_pt (U : Set ℝ) (x : ℝ) :=
  ∀ ε > 0, ∃ y ∈ Ioo (x - ε) (x + ε), y ∈ U \ {x}
 
--Def 11.4
def subsequence (a : ℕ → ℝ) (b : ℕ → ℝ) :=
  ∃ (n : ℕ → ℕ), ∀ k, n k < n (k + 1) ∧ b k = a (n k)


def lim_pt (a : ℕ → ℝ) (L : ℝ) :=
  ∃ (b : ℕ → ℝ), subsequence a b ∧ convto b L

def compact (K : Set ℝ) := 
∀ (a : ℕ → ℝ), in_set a K → ∃ L ∈ K, lim_pt a L


def open_cover (E : Set ℝ) (C : Set (Set ℝ)) := 
  ∀ U ∈ C, Open U ∧ E ⊆ ⋃ U ∈ C, U

def finite_subcover (E : Set ℝ) (C : Set (Set ℝ)) (F : ℕ → Set ℝ) := 
  ∃ (N : ℕ), (∀ n ∈ Finset.range N, F n ∈ C) ∧ (E ⊆ ⋃ n ∈ Finset.range N, F n)

def HB (E : Set ℝ) := 
  ∀ C, open_cover E C → ∃ F, finite_subcover E C F

end Definitions

section Theorems

variable {a b : ℕ → ℝ}
variable {L K c d : ℝ}

-- Prop 11.1
lemma open_interval : Open (Ioo c d) := by 
  unfold Open; intro x hx
  by_cases h : c > d
  use min ((x - c)/2) ((d - x)/2)  
  simp; constructor; exact hx
  intro y ys
  --by_cases h' : (x - c) / 2 > (d - x) / 2 
  --have : min ((x - c) / 2) ((d - x) / 2) = (d - x) / 2 := min_eq_right_of_lt h'
  --rw[this] at ys
  unfold Ioo at ys; rw [Set.mem_setOf] at ys
  unfold Ioo; rw [Set.mem_setOf]; constructor


theorem convto_subsequence_of_convto (sab : subsequence a b) (ca : convto a L) : convto b L := by
  intro ε εpos
  obtain ⟨N,hN⟩ := ca ε εpos
  use N; intro n hn
  obtain ⟨m,sab⟩ := sab
  obtain ⟨inc, eq⟩ := sab n
  rw[eq]
  have : m n ≥ n := by 
    clear! N eq
    induction' n with n ih
    exact Nat.zero_le (m 0)
    specialize ih (sab n).1
    calc 
      m (n + 1) = (m (n + 1) - m n) + m n := by refine (Nat.sub_eq_iff_eq_add ?_).mp rfl; exact le_of_lt (sab n).1
      _ ≥ 1 + n := by apply add_le_add; apply Nat.sub_pos_of_lt; exact (sab n).1; exact ih
      _ = n + 1 := by rw[add_comm]
  exact hN (m n) (by trans n; exact this; exact hn)

lemma unbounded_subsequence_of_unbounded (sab : subsequence a b) (ub : ¬ bounded a) : ¬ bounded b := by
sorry


end Theorems


-- CHAPTER 12 : Continuous Functions

section Definitions

variable {f g h : ℝ → ℝ}
variable {D K : Set ℝ}
variable {a b : ℕ → ℝ}
variable {L x y : ℝ}

def Im (a : ℕ → ℝ) :=
  {a n | n : ℕ}


def sq_continuous_on_at (f : ℝ → ℝ) (D : Set ℝ) (x : ℝ) := 
  x ∈ D → (∀ a, in_set a D → convto a x → convto (fun n ↦ f (a n)) (f x))

def sq_continuous_on (f : ℝ → ℝ) (D : Set ℝ) :=
  ∀ x, sq_continuous_on_at f D x

def continuous_on_at (f : ℝ → ℝ) (D : Set ℝ) (x : ℝ) := 
  x ∈ D → (∀ ε > 0, ∃ δ > 0, ∀ y ∈ D, |x - y| < δ → |f x - f y| < ε)

def continuous_on (f : ℝ → ℝ) (D : Set ℝ) := 
  ∀ x, continuous_on_at f D x

def top_continuous_on (f : ℝ → ℝ) (D : Set ℝ) :=
  ∀ K, K ⊆ D → Open (f '' K) → Open K


def unif_continuous_on (f : ℝ → ℝ) (D : Set ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, ∀ a ∈ D, |x - a| < δ → |f x - f a| < ε 

def flim_on_at_is (f : ℝ → ℝ) (D : Set ℝ) (x : ℝ) (L : ℝ) :=
  (∀ a, in_set a (D \ {x}) → convto a x → convto (fun n ↦ f (a n)) L)

end Definitions

section Theorems

variable {f g h : ℝ → ℝ}
variable {D Q : Set ℝ}
variable {a b : ℕ → ℝ}
variable {A L K x y : ℝ}

-- Prop 12.1 
theorem scalar_continuous {A : ℝ} (h : sq_continuous_on_at f D x) : sq_continuous_on_at (fun x ↦ A * f x) D x := by
  intro xD a aD cax
  specialize h xD a aD cax
  apply scalar_convto; exact h

theorem add_continuous (hf : sq_continuous_on_at f D x) (hg : sq_continuous_on_at g D x) : 
sq_continuous_on_at (fun x ↦ f x + g x) D x := by
  intro xD a aD cax
  specialize hf xD a aD cax
  specialize hg xD a aD cax
  apply add_convto <;> assumption

theorem mul_continuous (hf : sq_continuous_on_at f D x) (hg : sq_continuous_on_at g D x) : 
sq_continuous_on_at (fun x ↦ f x * g x) D x := by
  intro xD a aD cax
  specialize hf xD a aD cax
  specialize hg xD a aD cax
  apply mul_convto <;> assumption

theorem div_continuous (hf : sq_continuous_on_at f D x) (hg : sq_continuous_on_at g D x) (gn0 : g x ≠ 0) : 
sq_continuous_on_at (fun x ↦ f x / g x) (D \ {r : ℝ | g r = 0}) x := by
  intro xD a aDn cax
  have aD : in_set a D := by intro n; apply (aDn n).1
  specialize hf xD.1 a aD cax
  specialize hg xD.1 a aD cax
  dsimp; apply div_convto
  exact hf; exact hg
  intro n
  obtain ⟨aD, an0⟩ := aDn n
  exact an0
  exact gn0


--Prop 12.2
theorem scalar_flim {A : ℝ} (hf : flim_on_at_is f D y L) : flim_on_at_is (fun x ↦ A * f x) D y (A * L) := by
  intro a ainD cay 
  dsimp; apply scalar_convto
  apply hf 
  exact ainD; exact cay

theorem add_flim (hf : flim_on_at_is f D y L) (hg : flim_on_at_is g D y K) :
flim_on_at_is (fun x ↦ f x + g x) D y (L + K) := by 
  intro a ainD cay
  apply add_convto
  apply hf <;> assumption
  apply hg <;> assumption

theorem mul_flim (hf : flim_on_at_is f D y L) (hg : flim_on_at_is g D y K) :
flim_on_at_is (fun x ↦ f x * g x) D y (L * K) := by 
  intro a ainD cay
  apply mul_convto
  apply hf <;> assumption
  apply hg <;> assumption

theorem div_flim (hf : flim_on_at_is f D y L) (hg : flim_on_at_is g D y K) (Kn0 : K ≠ 0) :
flim_on_at_is (fun x ↦ f x / g x) (D \ {r : ℝ | g r = 0}) y (L / K) := by 
  intro a ainD cay
  have aD : in_set a (D \ {y}) := by intro n; exact ⟨(ainD n).1.1, (ainD n).2⟩
  apply div_convto
  apply hf <;> assumption
  apply hg <;> assumption
  intro n; exact (ainD n).1.2
  exact Kn0
  

--Thm 12.1
theorem continuous_eq : sq_continuous_on_at = continuous_on_at := by
  ext f D x
  -- unfold sq_continuous_on_at continuous_on_at
  constructor
  intro squeem
  intro xD; specialize squeem xD
  contrapose! squeem
  obtain ⟨ε, εpos, squeem⟩ := squeem
  set a : ℕ → ℝ := fun n ↦ (Classical.choose (squeem (1 / ((n : ℝ) + 1)) (by refine one_div_pos.mpr ?_ ; apply Nat.cast_add_one_pos  ))) with ha
  have ha' : in_set a D := by 
    intro n
    apply (Classical.choose_spec (squeem (1 / ((n : ℝ) + 1)) (by refine one_div_pos.mpr ?_ ; apply Nat.cast_add_one_pos  ))).1
  use a 
  constructor
  exact ha'
  have heb : ∀ n, |x - a n| < 1 / ((n : ℝ) + 1) := by 
    intro n
    rw[ha]; dsimp
    apply (Classical.choose_spec (squeem (1 / ((n : ℝ) + 1)) (by refine one_div_pos.mpr ?_ ; apply Nat.cast_add_one_pos  ))).2.1
  have bne : ∀ n, ε ≤ |f x - f (a n)| := by 
    intro n
    apply (Classical.choose_spec (squeem (1 / ((n : ℝ) + 1)) (by refine one_div_pos.mpr ?_ ; apply Nat.cast_add_one_pos  ))).2.2
  constructor
  intro ε εpos
  obtain ⟨N,⟨Npos,hN⟩⟩ := archify ε εpos
  use N; intro n hn
  trans 1 / ↑N
  calc
    |a n - x| < 1 / (↑n + 1) := by rw[← abs_neg]; simp; rw[inv_eq_one_div]; exact heb n
    _ ≤ 1 / (↑N + 1) := by
      have : (↑n + 1) ≥ (↑N + 1) := by apply Nat.add_le_add hn (le_refl 1)
      apply one_div_le_one_div_of_le; linarith; norm_cast
    _ ≤ 1 / ↑N := by refine one_div_le_one_div_of_le ?_ ?_; norm_cast; linarith
    _ = _ := rfl
  exact hN
  
  unfold convto; dsimp; push_neg
  use ε; constructor; exact εpos
  intro n; use n; constructor
  exact le_refl n
  rw[← abs_neg]; simp; exact bne n

  intro conman
  intro xD a aD cax
  intro ε εpos; dsimp
  unfold continuous_on_at at conman
  obtain ⟨δ, δpos, hδ⟩ := conman xD ε εpos
  specialize cax δ δpos
  obtain ⟨N,cax⟩ := cax
  use N; intro n hn
  specialize cax n hn
  have : a n ∈ D := aD n
  specialize hδ (a n) this
  rw[← abs_neg]; simp; apply hδ
  rw[← abs_neg]; simp; exact cax


theorem continuous_eq' : sq_continuous_on = continuous_on := by
  unfold sq_continuous_on continuous_on; rw[continuous_eq]


--Thm 12.2 
theorem intermediate_value {f : ℝ → ℝ} {a b y: ℝ} (h : sq_continuous_on f (Icc a b)) (hy : y ∈ Icc (f a) (f b)) (alb : a < b) :
  ∃ c ∈ Icc a b, f c = y := by 
  by_cases h' : f a = f b
  rw[h'] at hy
  use b; constructor
  constructor; exact le_of_lt alb; exact le_refl b; apply eq_of_le_of_le hy.1 hy.2
  by_cases mlem : y = f a ∨ y = f b
  obtain fay|bay := mlem
  use a; exact ⟨⟨le_refl a, le_of_lt alb⟩, by rw[fay]⟩
  use b; exact ⟨⟨le_of_lt alb, le_refl b⟩, by rw[bay]⟩
  push_neg at mlem
  have four : f a < y := by apply lt_of_le_of_ne; exact hy.1; symm; exact mlem.1
  have five : y < f b := by apply lt_of_le_of_ne; exact hy.2; exact mlem.2

  by_cases h'' : f a ≤ f b
  have falb : f a < f b :=  lt_of_le_of_ne h'' h'
  unfold sq_continuous_on at h
  have fay : y ≥ f a := hy.1
  have fby : y ≤ f b := hy.2


--Prop 12.4
theorem bounded_of_cont_of_compact (h : continuous_on f Q) (hb : compact Q) (nempty : ∃ x, x ∈ Q) : bounded f := by
  unfold bounded boundedby
  unfold compact at hb
  unfold continuous_on at h
  contrapose! h
  rw[← continuous_eq]
  unfold sq_continuous_on_at
  push_neg
  set a : ℕ → ℝ := fun n ↦ Classical.choose (h n) with ha
  obtain ⟨x,xQ⟩ := nempty
  use x
  constructor; exact xQ
  use a; constructor
  intro n; rw[ha]; dsimp
  
  


end Theorems