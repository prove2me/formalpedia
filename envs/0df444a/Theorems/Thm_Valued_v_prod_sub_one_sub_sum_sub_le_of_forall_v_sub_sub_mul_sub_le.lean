-- Prove2me | Theorems.Thm_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le
-- name    : Valued.v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/cb800627-5ed4-5a8a-9da1-22d897cc5b5c
-- title:
--   Ultrametric product estimate with Lipschitz quadratic remainder
-- statement:
--   Let $K$ be a field with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, and let $n, r$ be natural numbers. Given functions $F_{i j} : K \to K$ for $i \in \mathrm{Fin}\,n$, $j \in \mathrm{Fin}\,r$, and scalars $d_{i j} \in K$, assume: $v(d_{i j}) \le 1$ for all $i, j$; $F_{i j}(0) = 1$ for all $i, j$; and for all $i, j$, all $e, e' \in K$ and all $s, t \in \Gamma_0$ with $s < 1$, $v(e) \le s$, $v(e') \le s$ and $v(e - e') \le t$, one has $v\bigl(F_{i j}(e) - F_{i j}(e') - d_{i j}(e - e')\bigr) \le t s$. Write $R(\varepsilon)_j = \prod_i F_{i j}(\varepsilon_i) - 1 - \sum_i d_{i j}\varepsilon_i$ for $\varepsilon : \mathrm{Fin}\,n \to K$. The conclusion is a conjunction: first, $R(0)_j = 0$ for every $j$ (stated with the zero vector's coordinates written out); second, for all $\varepsilon, \varepsilon' : \mathrm{Fin}\,n \to K$ and all $s, t \in \Gamma_0$ with $s < 1$, $v(\varepsilon_i) \le s$, $v(\varepsilon'_i) \le s$ and $v(\varepsilon_i - \varepsilon'_i) \le t$ for every $i$, one has $v\bigl(R(\varepsilon)_j - R(\varepsilon')_j\bigr) \le t s$ for every $j$.
--
--   The statement says that a product of one-variable functions each approximated to first order by a linear form, with Lipschitz quadratic remainder, again has a Lipschitz quadratic remainder in the sup norm; this is exactly the hypothesis shape required by the non-archimedean Newton iteration, with matrix $d$ transposed. It is used in the Cerednik–Drinfeld material to solve systems $\prod_i F_{i j}(\varepsilon_i) = y_j$ coming from products of theta functions, in [`CerednikDrinfeld.Omega.exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt) and [`CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Valued.v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le
    {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {n r : ℕ} (F : Fin n → Fin r → K → K) (d : Fin n → Fin r → K)
    (hd : ∀ i j, Valued.v (d i j) ≤ 1)
    (hF0 : ∀ i j, F i j 0 = 1)
    (hF : ∀ (i : Fin n) (j : Fin r) (e e' : K) (s t : Γ₀), s < 1 → Valued.v e ≤ s → Valued.v e' ≤ s →
      Valued.v (e - e') ≤ t → Valued.v (F i j e - F i j e' - d i j * (e - e')) ≤ t * s) :
    (∀ j : Fin r, (∏ i, F i j ((0 : Fin n → K) i)) - 1 - ∑ i, d i j * (0 : Fin n → K) i = 0) ∧
    ∀ (ε ε' : Fin n → K) (s t : Γ₀), s < 1 → (∀ i, Valued.v (ε i) ≤ s) → (∀ i, Valued.v (ε' i) ≤ s) →
      (∀ i, Valued.v (ε i - ε' i) ≤ t) →
      ∀ j : Fin r, Valued.v (((∏ i, F i j (ε i)) - 1 - ∑ i, d i j * ε i) - ((∏ i, F i j (ε' i)) - 1 - ∑ i, d i j * ε' i))
        ≤ t * s := by sorry
