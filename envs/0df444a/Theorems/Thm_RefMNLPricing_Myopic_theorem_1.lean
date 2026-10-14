-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_theorem_1
-- name    : RefMNLPricing.Myopic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:19.564387+00:00
-- url     : https://prove2.me/theorems/4249592c-b93d-457b-b1f0-1e9c8c50be4f
-- title:
--   Theorem 1, p. 12 — the optimal single-period revenue Π^m(r) is the unique root of (13)
-- statement:
--   Consider the MNL pricing model with reference effects, with $b_i>0$, $c_i^\pm\ge0$, price box $\mathcal P^n = [0,p_H]^n$, $p_H>0$, and the ceiling assumption $p_H\ge\hat p_H$. Let $r\in\mathcal P^n$ and let $p$ be any maximiser of $\Pi(\cdot,r)$ over $\mathcal P^n$, so that $\Pi^m(r) = \Pi(p,r)$ is the optimal single-period revenue. With $\lambda_i$, $\gamma_i$ of Definition 3, consider the scalar equation
--
--   $$
--   \Pi = \sum_{i\in N_l}\lambda_i(\Pi,r_i) + \sum_{i\in N_n}\frac{1}{b_i+c_i}\exp\big(a_i-(b_i+c_i)\Pi + c_i r_i - 1\big) + \sum_{i\in N_g}\gamma_i(\Pi,r_i). \qquad (13)
--   $$
--
--   Then $\Pi^m(r)$ solves (13), and every solution $\Pi$ of (13) equals $\Pi^m(r)$.
--
--   The theorem turns the multi-dimensional, non-smooth and non-concave myopic optimisation into a one-dimensional root-finding problem.
--
--   **Formalization Note** "$\Pi^m(r)$ is the unique solution" is split into two conjuncts: $\Pi^m(r)$ is a solution, and every solution equals it. $\Pi^m(r)$ is represented as the revenue of an arbitrary maximiser, so no choice of maximiser is involved. The three sums of (13) are one sum over products split by type (see the definition of the right-hand side).
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 12, Theorem 1, (13); standing assumption §2.4, p. 11

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Definitions.Def_RefMNLPricing_Myopic_Equation13

namespace RefMNLPricing.Myopic

/-- Theorem 1, p. 12. Under the standing assumptions and the ceiling assumption `p_H ≥ p̂_H`, for
`r ∈ Pⁿ` and any maximiser `p` of `Π(·, r)` over `Pⁿ`, the optimal single-period revenue
`Π^m(r) = Π(p, r)` solves equation (13), `Π = rhs13 Π r`, and is its only solution. -/
theorem theorem_1 {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (r p : Fin n → ℝ) (hr : InBox pH r) (hp : IsBoxMax a b cp cm pH r p) :
    revenue a b cp cm p r = rhs13 a b cp cm (revenue a b cp cm p r) r ∧
      ∀ v : ℝ, v = rhs13 a b cp cm v r → v = revenue a b cp cm p r := by sorry

end RefMNLPricing.Myopic
