-- Prove2me | Theorems.Thm_SLPricing_Compare_myopic_comparison
-- name    : SLPricing.Compare.myopic_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:38.011632+00:00
-- url     : https://prove2.me/theorems/6a96c5cb-13bf-4aed-95b8-068a83842f8c
-- title:
--   Proof of Proposition 8, p. 34 — with SL and $\delta_c = 0$, $\pi^*_p < \pi^*_r$
-- statement:
--   In the presence of SL ($\gamma > 0$) and with myopic consumers ($\delta_c = 0$), let $\pi^*_p$ be the firm's optimal expected profit under pre-announced pricing and $\pi^*_r$ its optimal expected profit under responsive pricing, at the same parameters $\sigma_p, \gamma, c$. Then
--   $$\pi^*_p \;<\; \pi^*_r .$$
--
--   This is the endpoint $\delta_c = 0$ of Proposition 8: when consumers do not wait strategically, the firm's ability to react to reviews is worth strictly more than commitment.
--
--   **Formalization Note** Both values are suprema over all prices and all equilibria, in the extended reals; under responsive pricing the second-period rule must be optimal at every $q_u$ (no commitment). No existence of an optimal pre-announced plan is assumed.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Appendix A, proof of Proposition 8, p. 34

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Compare

/-- Appendix A, proof of Proposition 8, p. 34: in the presence of SL and for myopic consumers
(`δc = 0`), the firm's optimal expected profit under responsive pricing strictly exceeds its
optimal expected profit under pre-announced pricing: `π*_p < π*_r`. -/
theorem myopic_comparison (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (hδ : P.δc = 0) :
    preValue P < respValue P := by sorry

end SLPricing.Compare
