-- Prove2me | Theorems.Thm_ProbEffIS_GE_halfspace_bound
-- name    : ProbEffIS.GE.halfspace_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:48.264231+00:00
-- url     : https://prove2.me/theorems/00c17ea2-7656-45a1-82da-55b0af127cee
-- title:
--   Proof of Theorem 2 — rate bound on a dominating half-space
-- statement:
--   Let $s$ lie in the interior effective domain of $\mu$ and satisfy $\nabla\mu(s)=a$. The proof of Theorem 2 states
--
--   $$
--   I(a)=s^\top a-\mu(s),\qquad s^\top(x-a)\ge0\Longrightarrow I(x)\ge I(a).
--   $$
--
--   This identifies the rate of a dominating point and bounds the rate throughout its associated half-space. It is the local comparison used to obtain the minimum over a finite dominating set.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 48, proof of Theorem 2

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- The half-space inequality in the proof of Theorem 2, p. 48. -/
theorem halfspace_bound {d : ℕ} (ν : ℝ → Measure (Rd d))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (s a : Rd d) (hs : s ∈ interior (dom μ)) (hsa : gradE μ s = a) :
    rate μ a = ((inner ℝ s a : ℝ) : EReal) - μ s ∧
    ∀ x : Rd d, 0 ≤ inner ℝ s (x - a) → rate μ a ≤ rate μ x := by sorry

end ProbEffIS.GE
