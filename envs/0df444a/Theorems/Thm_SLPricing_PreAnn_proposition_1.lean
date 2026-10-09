-- Prove2me | Theorems.Thm_SLPricing_PreAnn_proposition_1
-- name    : SLPricing.PreAnn.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:44.926376+00:00
-- url     : https://prove2.me/theorems/032bbd55-e2c0-4d17-b034-f18b81bda09a
-- title:
--   Proposition 1, p. 12 — without social learning, $\pi^* = (1-c)^2/(\delta_c+3)$ at $p_1^*=(c(1+\delta_c)+2)/(\delta_c+3)$, $p_2^*=(2c+\delta_c+1)/(\delta_c+3)$
-- statement:
--   In the absence of social learning ($\gamma=0$), with $c\in[0,1)$ and $\delta_c\in[0,1]$:
--
--   1. the optimal pre-announced profit is
--   $$\pi^*=\frac{(1-c)^2}{\delta_c+3};$$
--   2. the plan
--   $$p_1^*=\frac{c(1+\delta_c)+2}{\delta_c+3},\qquad p_2^*=\frac{2c+\delta_c+1}{\delta_c+3}$$
--   is optimal;
--   3. if $\delta_c<1$, it is the only optimal plan;
--   4. $p_1^*$ is strictly decreasing and $p_2^*$ strictly increasing in $\delta_c\in[0,1]$;
--   5. the optimal profit is strictly decreasing in $\delta_c\in[0,1]$.
--
--   This is the classical benchmark (Landsberger and Meilijson 1985) against which the effect of social learning is measured.
--
--   **Formalization Note** The optimal profit is the supremum over all real plans and all purchasing equilibria (in the extended reals); "optimal plan" means that some equilibrium of the plan attains it. The paper's uniqueness claim is restricted to $\delta_c<1$: at $\delta_c=1$ every plan with $p_1=(1+c)/2\le p_2$ is also optimal. The clause "any pre-announced price plan generates a unique equilibrium" is the separate item for (2).
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 1, p. 12; proof outline, p. 28

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Proposition 1, p. 12 (proof outline p. 28): without social learning (`γ = 0`) the optimal
pre-announced profit is `π* = (1 − c)²/(δc + 3)`, attained by the plan
`p₁* = (c(1 + δc) + 2)/(δc + 3)`, `p₂* = (2c + δc + 1)/(δc + 3)`; for `δc < 1` this is the only
optimal plan; `p₁*` is strictly decreasing and `p₂*` strictly increasing in `δc ∈ [0, 1]`, and
the optimal profit is strictly decreasing in `δc ∈ [0, 1]`. -/
theorem proposition_1 (P : Params) (hP : P.Standing) :
    preValue P.noSL = (((1 - P.c) ^ 2 / (P.δc + 3) : ℝ) : EReal) ∧
      IsOptimalPre P.noSL ((P.c * (1 + P.δc) + 2) / (P.δc + 3))
        ((2 * P.c + P.δc + 1) / (P.δc + 3)) ∧
      (P.δc < 1 → ∀ p₁ p₂ : ℝ, IsOptimalPre P.noSL p₁ p₂ →
        p₁ = (P.c * (1 + P.δc) + 2) / (P.δc + 3) ∧ p₂ = (2 * P.c + P.δc + 1) / (P.δc + 3)) ∧
      StrictAntiOn (fun d : ℝ => (P.c * (1 + d) + 2) / (d + 3)) (Icc 0 1) ∧
      StrictMonoOn (fun d : ℝ => (2 * P.c + d + 1) / (d + 3)) (Icc 0 1) ∧
      StrictAntiOn (fun d : ℝ => preValue (P.withδc d).noSL) (Icc 0 1) := by sorry

end SLPricing.PreAnn
