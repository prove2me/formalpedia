-- Prove2me | Theorems.Thm_SLPricing_PreAnn_preValue_continuous
-- name    : SLPricing.PreAnn.preValue_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:26.092241+00:00
-- url     : https://prove2.me/theorems/8c4f2e89-df24-4232-ad06-febbd5ebf5a7
-- title:
--   Proof of Proposition 3, p. 30 — the optimal pre-announced profit $\pi_p^*$ is finite and continuous in $\delta_c\in[0,1]$
-- statement:
--   Assume social learning is present, $\gamma>0$, and fix $\sigma_p$, $\gamma$ and $c$. For $d\in[0,1]$ let $\pi_p^*(d)$ be the optimal pre-announced profit when the consumers' discount factor is $\delta_c=d$. Then $\pi_p^*(d)$ is a finite real number for every $d\in[0,1]$, and
--   $$d\ \longmapsto\ \pi_p^*(d)\quad\text{is continuous on }[0,1].$$
--
--   The paper derives this from Berge's Maximum Theorem. Together with the strict comparisons at $\delta_c=0$ (Example 2) and at $\delta_c=1$ (Propositions 1 and 2), it yields the thresholds of Proposition 3.
--
--   **Formalization Note** The optimal value is a supremum in the extended reals; the statement asserts that it is a real number $V(d)$ for each $d\in[0,1]$ and that $V$ is continuous on $[0,1]$.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Appendix A, proof of Proposition 3, p. 30

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Appendix A, proof of Proposition 3, p. 30: with social learning (`γ > 0`) the firm's optimal
pre-announced profit `π*_p` is finite for every `δc ∈ [0, 1]` and continuous in `δc` on `[0, 1]`
(`σp`, `γ`, `c` fixed). -/
theorem preValue_continuous (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ V : ℝ → ℝ, ContinuousOn V (Icc 0 1) ∧
      ∀ d ∈ Icc (0 : ℝ) 1, preValue (P.withδc d) = ((V d : ℝ) : EReal) := by sorry

end SLPricing.PreAnn
