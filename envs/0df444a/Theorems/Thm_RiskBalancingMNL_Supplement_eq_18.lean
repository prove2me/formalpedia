-- Prove2me | Theorems.Thm_RiskBalancingMNL_Supplement_eq_18
-- name    : RiskBalancingMNL.Supplement.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:57:04.69251+00:00
-- url     : https://prove2.me/theorems/f2b42ca8-6861-4985-9fd3-c9be02d29f92
-- title:
--   Eq. (18) — the first-order condition $(m_j-1/\hat b_j-\pi/\lambda)^2=(1/\hat b_j)^2+\theta$ at every optimum
-- statement:
--   Consider the MNL model with asymmetric price sensitivities $\hat b_i>0$ and a risk weight $\lambda\in(0,1)$. Let $m$ be an optimal markup vector of problem (6), and let $\pi$, $q_i$, $q_0$ be its expected profit and choice probabilities. With
--   $$
--   \theta=\Big(\frac\pi\lambda\Big)^2+2\sum_{i=1}^n\frac{(m_i-\pi/\lambda)\,q_i}{\hat b_i\,q_0},
--   $$
--   every product $j$ satisfies
--   $$
--   \Big(m_j-\frac1{\hat b_j}-\frac\pi\lambda\Big)^2=\Big(\frac1{\hat b_j}\Big)^2+\theta .
--   $$
--   Since $\theta$ does not depend on $j$, this links the optimal markups of all products through two scalars, $\pi$ and $\theta$; it is the equation that Theorem 2 solves.
--
--   **Formalization Note** Optimality is over all markup vectors with $\pi\ge0$. Assumption 1 is not assumed.
--
--   Differences from the source:
--   - generalization: (18) under Assumption 1, standing for the rest of §5 → (18) at every optimal markup vector, without Assumption 1; reason: if π > 0 the constraint is slack and the gradient of L vanishes, which gives (18); if π = 0 then m = 0 and θ = 0, where (18) holds; the source's case is the special case satisfying Assumption 1
--   - reading: λ ∈ [0, 1) (problem (5)) → 0 < λ < 1; reason: θ contains π/λ, undefined at λ = 0
--   - encoding: problem (6) over share vectors q → IsOptimal over all markup vectors m ∈ ℝⁿ with π(m) ≥ 0; reason: the paper's one-to-one map between markups and shares (p.9), as in the published base mission
--   - encoding: primitives a_i, y_i, b, β of (16) → reduced form â_i, b̂_i > 0, c_i; reason: the primitives enter only through â_i = a_i + y_i and b̂_i = b − βy_i, and every positive b̂ arises
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5.1, definition of $\theta$ and (18), p.15

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_AsymParams

namespace RiskBalancingMNL.Supplement

/-- **Eq. (18), the first-order condition of the asymmetric MNL problem**, Li & Webster,
*Optimizing Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14),
§5.1, p.15: with `θ := (π/λ)² + 2 Σᵢ (mᵢ − π/λ)qᵢ/(b̂ᵢq₀)`,
`(mⱼ − 1/b̂ⱼ − π/λ)² = (1/b̂ⱼ)² + θ` for every product `j`.

Stated at every optimal markup vector `m` of problem (6) for `λ ∈ (0, 1)`, with `π`, `qᵢ`, `q₀`
and `θ` evaluated at `m`.

**Formalization Note** Optimality is over all of `ℝⁿ` under `π ≥ 0`. Assumption 1 (p.15) is not
assumed: the identity holds at every optimum. `λ > 0` because `π/λ` is undefined at `λ = 0`. -/
theorem eq_18 {n : ℕ} (P : AsymParams n) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (m : Fin n → ℝ) (hm : P.IsOptimal lam m) (j : Fin n) :
    (m j - 1 / P.bHat j - P.profit m / lam) ^ 2 = (1 / P.bHat j) ^ 2 + P.theta lam m := by sorry

end RiskBalancingMNL.Supplement
