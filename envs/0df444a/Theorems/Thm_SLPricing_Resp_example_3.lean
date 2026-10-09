-- Prove2me | Theorems.Thm_SLPricing_Resp_example_3
-- name    : SLPricing.Resp.example_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:48.585695+00:00
-- url     : https://prove2.me/theorems/cb55b339-60e8-43df-8c83-4af15b4a6a10
-- title:
--   Example 3, p. 23 — with myopic consumers, SL strictly raises the optimal responsive profit
-- statement:
--   Consider responsive pricing with myopic consumers, $\delta_c=0$. Let $\pi_r^*|_{\gamma=k}$ be the firm's optimal expected profit when the SL influence parameter is $\gamma=k>0$, and $\pi_r^*|_{\gamma\to0}$ the optimal expected profit without social learning. Then
--   $$\pi_r^*|_{\gamma=k}\ >\ \pi_r^*|_{\gamma\to0}.$$
--
--   This is the endpoint $\delta_c=0$ of Proposition 6.
--
--   **Formalization Note** The benchmark "absence of SL" ($\gamma\to0$) is the same model at $\gamma=0$, where the posterior mean is $0$ with certainty. Both optimal values are suprema in the extended reals over all first-period prices and all their equilibria.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Example 3, p. 23 (proof p. 33)

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- Example 3, p. 23 (proof p. 33): with myopic consumers (`δc = 0`), the optimal expected
profit under responsive pricing with social learning (`γ > 0`) strictly exceeds the optimal
profit without it (`γ = 0`). -/
theorem example_3 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (hδ : P.δc = 0) :
    respValue P.noSL < respValue P := by sorry

end SLPricing.Resp
