-- Prove2me | Theorems.Thm_SLPricing_PreAnn_example_2
-- name    : SLPricing.PreAnn.example_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:17.672916+00:00
-- url     : https://prove2.me/theorems/ffec1073-da70-440e-bdf9-45013b781623
-- title:
--   Example 2, p. 17 — myopic consumers: $\pi_p^*|_{\gamma=k} > \pi_p^*|_{\gamma\to 0}$
-- statement:
--   Suppose consumers are myopic, $\delta_c=0$. Then for every SL influence $\gamma=k>0$ the optimal pre-announced profit with social learning strictly exceeds the optimal pre-announced profit without it:
--   $$\pi_p^*\big|_{\gamma=k}>\pi_p^*\big|_{\gamma\to 0}.$$
--
--   This isolates the informational effect of social learning: without the behavioural effect (consumers do not wait), the firm can always exploit the spread of second-period valuations. It is the $\delta_c=0$ end of Proposition 3.
--
--   **Formalization Note** Both optimal values are suprema over all plans and all purchasing equilibria in the extended reals; the benchmark $\gamma\to 0$ is the same model at $\gamma=0$.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Example 2, p. 17; proof, p. 31

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Example 2, p. 17 (proof p. 31): with myopic consumers (`δc = 0`), the optimal pre-announced
profit with social learning (`γ > 0`) strictly exceeds the optimal profit without it (`γ = 0`). -/
theorem example_2 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (hδ : P.δc = 0) :
    preValue P.noSL < preValue P := by sorry

end SLPricing.PreAnn
