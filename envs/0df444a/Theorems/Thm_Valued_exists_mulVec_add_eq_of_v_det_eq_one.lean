-- Prove2me | Theorems.Thm_Valued_exists_mulVec_add_eq_of_v_det_eq_one
-- name    : Valued.exists_mulVec_add_eq_of_v_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/dc6a3b34-0dba-522b-852c-d3d3825ca0d1
-- title:
--   Ultrametric Newton lemma: unimodular linear map plus small perturbation is onto
-- statement:
--   Let $K$ be a field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete for the induced topology, and assume the rank-one hypothesis that for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $m \in \mathbb{N}$ with $v(x)^m \le v(y)$. Let $n \in \mathbb{N}$ and let $A$ be an $n \times n$ matrix over $K$ all of whose entries satisfy $v(A_{ij}) \le 1$ and whose determinant satisfies $v(\det A) = 1$. Let $R : K^n \to K^n$ be any map (no continuity or algebraicity assumed) with $R(0) = 0$ satisfying the following quadratic Lipschitz estimate: for all $\varepsilon, \varepsilon' \in K^n$ and all $s, t \in \Gamma_0$ with $s < 1$, if $v(\varepsilon_j) \le s$ and $v(\varepsilon'_j) \le s$ for every coordinate $j$, and $v(\varepsilon_j - \varepsilon'_j) \le t$ for every $j$, then $v(R(\varepsilon)_i - R(\varepsilon')_i) \le t \cdot s$ for every $i$. Then for every $y \in K^n$ and every $s \in \Gamma_0$ with $s < 1$ and $v(y_i) \le s$ for all $i$, there exists $\varepsilon \in K^n$ with $v(\varepsilon_i) \le s$ for all $i$ and $A\varepsilon + R(\varepsilon) = y$, where $A\varepsilon$ denotes the matrix–vector product.
--
--   This is the several-variable Newton–Hensel (ultrametric implicit function) lemma in the form needed here: an integral unimodular linear map perturbed by a term that contracts by the factor $s$ surjects onto the polydisc of radius $s < 1$. It is used in the Čerednik–Drinfeld layer, in [`CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt) and its variant avoiding prescribed Möbius images, to solve for points whose theta-multipliers realise a given system of values close to $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valued_exists_mulVec_add_eq_of_v_det_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Valued.exists_mulVec_add_eq_of_v_det_eq_one
    {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ m : ℕ, Valued.v x ^ m ≤ Valued.v y)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j : Fin n, Valued.v (A i j) ≤ 1)
    (hdet : Valued.v A.det = 1)
    (R : (Fin n → K) → (Fin n → K)) (hR0 : R 0 = 0)
    (hR : ∀ (ε ε' : Fin n → K) (s t : Γ₀), s < 1 → (∀ j, Valued.v (ε j) ≤ s) → (∀ j, Valued.v (ε' j) ≤ s) →
      (∀ j, Valued.v (ε j - ε' j) ≤ t) → ∀ i, Valued.v (R ε i - R ε' i) ≤ t * s)
    (y : Fin n → K) (s : Γ₀) (hs : s < 1) (hy : ∀ i, Valued.v (y i) ≤ s) :
    ∃ ε : Fin n → K, (∀ i, Valued.v (ε i) ≤ s) ∧ A.mulVec ε + R ε = y := by sorry
