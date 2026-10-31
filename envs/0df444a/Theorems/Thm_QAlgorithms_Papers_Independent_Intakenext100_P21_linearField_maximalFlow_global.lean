-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P21_linearField_maximalFlow_global
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P21.linearField_maximalFlow_global
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:45:59.292136+00:00
-- url     : https://prove2.me/theorems/3895e3b4-dd2f-49a5-839b-867423e9b837
-- title:
--   A locally integrable continuous linear vector field is complete
-- statement:
--   Let $V$ be a Hausdorff locally convex real topological vector space and $D:V\to V$ a continuous linear map. If the smooth vector field $X(v)=Dv$ is locally integrable, its maximal local flow is global:
--
--   $$
--   D_X=\mathbb R\times V.
--   $$
--
--   The result concerns the maximal flow, so restricting a global flow to a smaller time domain does not contradict it. No Banach or completeness assumption is imposed on $V$.
-- source:
--   Integrability of unitary representations on reproducing kernel spaces, arXiv:1406.2681v3, PDF p. 10, Proposition 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P21

namespace QAlgorithms.Papers.Independent.Intakenext100.P21

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22 (BastianiSmoothOn BastianiAtlas)

open QAlgorithms.Papers.Independent.Next46.P15 (HasDirectionalDerivative directionalDerivative)

attribute [local instance] Classical.propDecidable

universe u v w

section LinearFields

variable {V : Type u} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

/-- Proposition 2.9, PDF p. 10: a locally integrable continuous linear
vector field has a global maximal flow. V can be nonnormable; no general
existence or uniqueness theorem for arbitrary locally convex ODEs is assumed. -/
theorem linearField_maximalFlow_global
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V] [T2Space V]
    (D : V →L[ℝ] V) (hD : IsLocallyIntegrable (linearField D)) :
    (maximalFlow (linearField D)).domain = Set.univ := by sorry

end LinearFields

end QAlgorithms.Papers.Independent.Intakenext100.P21
