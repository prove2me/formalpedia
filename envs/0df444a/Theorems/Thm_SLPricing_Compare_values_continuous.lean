-- Prove2me | Theorems.Thm_SLPricing_Compare_values_continuous
-- name    : SLPricing.Compare.values_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:34.893753+00:00
-- url     : https://prove2.me/theorems/10d86238-335a-4df5-b3cf-1ba0f879e4e5
-- title:
--   Proof of Proposition 8, p. 34 — with SL, $\pi^*_p$ and $\pi^*_r$ are finite and continuous in $\delta_c \in [0,1]$
-- statement:
--   In the presence of SL ($\gamma > 0$), with $\sigma_p$ and $c$ fixed, write $\pi^*_p(\delta_c)$ and $\pi^*_r(\delta_c)$ for the firm's optimal expected profits under pre-announced and responsive pricing when the consumers' discount factor is $\delta_c$. Then both are finite for every $\delta_c \in [0,1]$, and
--   $$\delta_c \mapsto \pi^*_p(\delta_c), \qquad \delta_c \mapsto \pi^*_r(\delta_c)$$
--   are continuous on $[0,1]$.
--
--   The paper attributes this to the continuity of both profit functions in $\delta_c$ and the Maximum Theorem; combined with the strict comparison at $\delta_c = 0$ it yields the threshold of Proposition 8.
--
--   **Formalization Note** The optimal values are extended-real suprema; the statement asserts real-valued continuous functions $V, W$ on $[0,1]$ that they equal.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Appendix A, proof of Proposition 8, p. 34

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Compare

/-- Appendix A, proof of Proposition 8, p. 34: in the presence of SL, the optimal expected profits
`π*_p` (pre-announced) and `π*_r` (responsive) are finite and continuous functions of the
consumers' discount factor `δc ∈ [0, 1]`. -/
theorem values_continuous (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    (∃ V : ℝ → ℝ, ContinuousOn V (Icc 0 1) ∧
      ∀ d ∈ Icc (0 : ℝ) 1, preValue (P.withδc d) = ((V d : ℝ) : EReal)) ∧
    (∃ W : ℝ → ℝ, ContinuousOn W (Icc 0 1) ∧
      ∀ d ∈ Icc (0 : ℝ) 1, respValue (P.withδc d) = ((W d : ℝ) : EReal)) := by sorry

end SLPricing.Compare
