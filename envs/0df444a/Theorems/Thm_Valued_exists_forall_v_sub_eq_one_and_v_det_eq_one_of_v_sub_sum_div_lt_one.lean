-- Prove2me | Theorems.Thm_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one
-- name    : Valued.exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/06baae8f-8865-58b9-abc0-93917df8dceb
-- title:
--   Generic centres make a partial-fraction matrix unimodular
-- statement:
--   Let $K$ be an algebraically closed field carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$, let $\iota$ be a finite index type, and let $t : \iota \to K$ satisfy $v(t_a) \le 1$ for all $a$ and $1 \le v(t_a - t_{a'})$ whenever $a \ne a'$. Fix $r \in \mathbb{N}$, integers $m_{ij}(a)$ for $i, j \in \mathrm{Fin}\,r$ and $a \in \iota$, and a choice of indices $a_0 : \mathrm{Fin}\,r \to \iota$ such that the matrix over $K$ with entries the images of $m_{ij}(a_0(i))$ has determinant of valuation exactly $1$. Then for every family of finite subsets $S_i \subseteq K$ ($i \in \mathrm{Fin}\,r$) there exist $b_0, \dots, b_{r-1} \in K$ with $v(b_i) \le 1$, with $v(b_i - t_a) = 1$ for all $i$ and all $a \in \iota$, and with $1 \le v(b_i - s)$ for all $s \in S_i$, such that every matrix $d \in M_r(K)$ satisfying $$v\Bigl(d_{ij} - \sum_{a \in \iota} \frac{m_{ij}(a)}{b_i - t_a}\Bigr) < 1 \quad \text{for all } i, j$$ has $v(\det d) = 1$.
--
--   An elementary valuation-theoretic statement of the form needed to produce centres at which a matrix of logarithmic derivatives of theta units, read off as a partial-fraction matrix of integer slope data, is unimodular; the finite sets $S_i$ allow finitely many centres to be avoided in each row. It is used in the unimodular-tangent step of the Jacobi inversion argument on $\Omega$, via [`CerednikDrinfeld.Omega.exists_v_det_eq_one_of_isUnit_det_pathCycle_of_finite`](thm.html#CerednikDrinfeld.Omega.exists_v_det_eq_one_of_isUnit_det_pathCycle_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Valued.exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {ι : Type} [Fintype ι] (t : ι → K)
    (ht : ∀ a : ι, Valued.v (t a) ≤ 1) (htsep : ∀ a a' : ι, a ≠ a' → 1 ≤ Valued.v (t a - t a'))
    {r : ℕ} (m : Fin r → Fin r → ι → ℤ) (a₀ : Fin r → ι)
    (hdet : Valued.v (Matrix.of (fun i j : Fin r => ((m i j (a₀ i) : ℤ) : K))).det = 1)
    (S : Fin r → Finset K) :
    ∃ b : Fin r → K,
      (∀ i, Valued.v (b i) ≤ 1) ∧
      (∀ i a, Valued.v (b i - t a) = 1) ∧
      (∀ i, ∀ s ∈ S i, 1 ≤ Valued.v (b i - s)) ∧
      ∀ d : Matrix (Fin r) (Fin r) K,
        (∀ i j, Valued.v (d i j - ∑ a, (m i j a : K) / (b i - t a)) < 1) →
        Valued.v d.det = 1 := by sorry
