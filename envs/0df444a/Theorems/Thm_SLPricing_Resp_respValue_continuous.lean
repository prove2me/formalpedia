-- Prove2me | Theorems.Thm_SLPricing_Resp_respValue_continuous
-- name    : SLPricing.Resp.respValue_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:55.632754+00:00
-- url     : https://prove2.me/theorems/a7415693-6dd6-4eb1-8e11-7b76dd3528df
-- title:
--   Appendix A, proof of Proposition 6, p. 33 — with SL, the optimal responsive profit $\pi^*_r$ is finite and continuous in $\delta_c\in[0,1]$
-- statement:
--   Consider responsive pricing with social learning ($\gamma>0$), and fix $\sigma_p$, $\gamma$ and $c$. For $d\in[0,1]$ let $\pi_r^*(d)$ be the firm's optimal expected profit when consumers discount by $\delta_c=d$. Then $\pi_r^*(d)$ is a finite real number for every $d\in[0,1]$, and
--   $$d\ \longmapsto\ \pi_r^*(d)\quad\text{is continuous on }[0,1].$$
--
--   The paper invokes this (via the Maximum Theorem) to pass from the endpoints $\delta_c=0$ and $\delta_c=1$ to the thresholds of Proposition 6.
--
--   **Formalization Note** The optimal value is a supremum in the extended reals; the statement asserts that it is the real value of a function continuous on $[0,1]$.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Appendix A, proof of Proposition 6, p. 33

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- Appendix A, proof of Proposition 6, p. 33: with social learning (`γ > 0`) the firm's optimal
expected profit under responsive pricing `π*_r` is finite for every `δc ∈ [0, 1]` and continuous
in `δc` on `[0, 1]` (`σp`, `γ`, `c` fixed). -/
theorem respValue_continuous (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ V : ℝ → ℝ, ContinuousOn V (Icc 0 1) ∧
      ∀ d ∈ Icc (0 : ℝ) 1, respValue (P.withδc d) = ((V d : ℝ) : EReal) := by sorry

end SLPricing.Resp
