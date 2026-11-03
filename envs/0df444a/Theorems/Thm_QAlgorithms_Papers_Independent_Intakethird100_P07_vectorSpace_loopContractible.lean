-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_vectorSpace_loopContractible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.vectorSpace_loopContractible
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:21:51.084272+00:00
-- url     : https://prove2.me/theorems/64b0820b-ae83-439a-aa7d-cef94c1dbcce
-- title:
--   Example 5.2
-- statement:
--   Let $V$ be a real topological vector space, with no norm, local convexity or completeness assumption. For $v\in V$ and $t\in[0,1]$ set $\Phi(v,t)=tv$. This is a continuous homotopy through additive endomorphisms and
--
--   $$\Phi(v,0)=0,\qquad\Phi(v,1)=v,\qquad\Phi(v+w,t)=\Phi(v,t)+\Phi(w,t).$$
--
--   Reversing time gives a contraction to zero. Thus $V$ is loop contractible.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 20, Example 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Example 5.2, PDF p. 20: scalar multiplication is a loop contraction
of every real topological vector space, with no norm or completeness requirement. -/
theorem vectorSpace_loopContractible
    (V : Type u) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] :
    IsAddLoopContraction (scalarHomotopy (V := V)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
