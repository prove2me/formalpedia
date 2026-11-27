-- Prove2me | Theorems.Thm_RiskBalancingMNL_Supplement_theorem_2
-- name    : RiskBalancingMNL.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:57:50.466264+00:00
-- url     : https://prove2.me/theorems/7e66cd9a-e591-513c-834a-bc700659e431
-- title:
--   Theorem 2 — optimal markups $m_j=1/\hat b_j+\pi/\lambda-\sqrt{(1/\hat b_j)^2+\theta}$ under asymmetric price sensitivity
-- statement:
--   Consider the MNL model with asymmetric price sensitivities $\hat b_i>0$ and a risk weight $\lambda\in(0,1)$. Let $m$ be an optimal markup vector of problem (6) that satisfies Assumption 1, $\lambda\le\pi/m_{\max}$, and let $\pi$ and $\theta=(\pi/\lambda)^2+2\sum_i(m_i-\pi/\lambda)q_i/(\hat b_iq_0)$ be evaluated at $m$. Then for every product $j$
--   $$
--   m_j=\frac1{\hat b_j}+\frac\pi\lambda-\sqrt{\Big(\frac1{\hat b_j}\Big)^2+\theta}. \tag{19}
--   $$
--   Neither the optimal markups nor the adjusted markups $m_j-1/\hat b_j$ are then equal across products, unlike the profit-maximizing solution; their order follows the order of the $\hat b_j$ (Theorem 3).
--
--   **Formalization Note** Assumption 1 is written $\lambda m_i\le\pi$ for every $i$. Optimality is over all markup vectors with $\pi\ge0$.
--
--   Differences from the source:
--   - generalization: Assumption 1: λ ≤ π*/m*_max at the optimum → λ · m_i ≤ π(m) for every i; reason: equivalent when m*_max > 0; at m = 0, where the printed quotient is undefined, the Lean hypothesis holds and (19) holds (θ = 0)
--   - reading: λ ∈ [0, 1) (problem (5)) → 0 < λ < 1; reason: θ contains π/λ, undefined at λ = 0
--   - encoding: problem (6) over share vectors q → IsOptimal over all markup vectors m ∈ ℝⁿ with π(m) ≥ 0; reason: the paper's one-to-one map between markups and shares (p.9), as in the published base mission
--   - encoding: primitives a_i, y_i, b, β of (16) → reduced form â_i, b̂_i > 0, c_i; reason: the primitives enter only through â_i = a_i + y_i and b̂_i = b − βy_i, and every positive b̂ arises
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5.1, Theorem 2 and (19), p.15; Assumption 1, p.15

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_AsymParams

namespace RiskBalancingMNL.Supplement

/-- **Theorem 2 (Optimal Markups in Risk-balancing Solution)**, Li & Webster, *Optimizing
Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), p.15: the
optimal markups are `mⱼ = 1/b̂ⱼ + π/λ − √((1/b̂ⱼ)² + θ)` for all `j` (19).

Stated for `λ ∈ (0, 1)` and every optimal markup vector `m` of problem (6) that satisfies
Assumption 1 (p.15), with `π` and `θ` evaluated at `m`.

**Formalization Note** Assumption 1, `λ ≤ π*/m*_max`, is encoded as `λ mᵢ ≤ π` for every `i`;
the two agree when `m*_max > 0`, and at `m = 0` (where the printed quotient is undefined) the
encoding holds trivially. -/
theorem theorem_2 {n : ℕ} (P : AsymParams n) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (m : Fin n → ℝ) (hm : P.IsOptimal lam m) (hA1 : ∀ i, lam * m i ≤ P.profit m) :
    ∀ j, m j = 1 / P.bHat j + P.profit m / lam - Real.sqrt ((1 / P.bHat j) ^ 2 + P.theta lam m) := by sorry

end RiskBalancingMNL.Supplement
