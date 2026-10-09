-- Prove2me | Theorems.Thm_SLPricing_PreAnn_lemma_5
-- name    : SLPricing.PreAnn.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:40.516293+00:00
-- url     : https://prove2.me/theorems/61b79d31-3f3e-4ae3-84de-bb70714a8f6e
-- title:
--   Lemma 5, p. 30 — the second-period expected utility is strictly increasing in the number of first-period buyers
-- statement:
--   Assume $\gamma>0$ and $\delta_c>0$. For a consumer of type $x$ facing second-period price $p_2$, let
--   $$v_2(n_1)=\delta_c\,\mathbb E\big[(x+q_u-p_2)^+\big],\qquad q_u\sim N\!\left(0,\ \sigma_p^2\frac{n_1\gamma}{n_1\gamma+1}\right),$$
--   be her second-period expected utility when a mass $n_1$ of consumers buys in the first period. Then $v_2$ is strictly increasing in $n_1\in[0,1]$, for every type $x$ and every price $p_2$.
--
--   This is the free-riding externality: each additional early buyer generates a review, which makes waiting more valuable for everyone else.
--
--   **Formalization Note** The hypothesis $\delta_c>0$ is added: at $\delta_c=0$ the second-period utility is identically $0$ and cannot be strictly increasing. The first-period price $p_1$ does not enter the second-period utility.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Appendix A, Lemma 5, p. 30

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Lemma 5, p. 30: a customer's second-period expected utility
`δc E[(x + q_u − p₂)⁺]`, with `q_u` distributed by the pre-posterior law for a mass `n₁` of
first-period buyers, is strictly increasing in `n₁ ∈ [0, 1]` (with social learning, `γ > 0`, and
`δc > 0`), for every type `x` and every second-period price `p₂`. -/
theorem lemma_5 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (hδ : 0 < P.δc) (p₂ x : ℝ) :
    StrictMonoOn (fun n₁ : ℝ => P.δc * ∫ q, max (x + q - p₂) 0 ∂(prePost P n₁)) (Icc 0 1) := by sorry

end SLPricing.PreAnn
