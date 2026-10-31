-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P21_maximalFlow_exists_unique
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P21.maximalFlow_exists_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:45:13.480179+00:00
-- url     : https://prove2.me/theorems/9a51d9ab-0b31-4880-9c45-3735605b0c2e
-- title:
--   The maximal local flow constructed from integral curves
-- statement:
--   Let $M$ be a Hausdorff smooth manifold modeled on a Hausdorff locally convex real space, with smoothness understood in the Bastiani calculus. Let $X$ be a locally integrable smooth vector field. For each $m$, let $I_m$ be the union of all open intervals containing zero on which an integral curve of $X$ starts at $m$, and let $\gamma_m$ be the curve obtained by gluing their coincident values. Then
--
--   $$
--   D_X=\{(t,m):t\in I_m\},\qquad \Phi^X(t,m)=\gamma_m(t)
--   $$
--
--   is an open domain and a smooth local flow with velocity $X$. This flow is unique among local flows on $D_X$ with velocity $X$.
--
--   This constructs the maximal flow from the vector field; uniqueness does not exclude restrictions to smaller domains.
-- source:
--   Integrability of unitary representations on reproducing kernel spaces, arXiv:1406.2681v3, PDF p. 8, Theorem 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P21

namespace QAlgorithms.Papers.Independent.Intakenext100.P21

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22 (BastianiSmoothOn BastianiAtlas)

open QAlgorithms.Papers.Independent.Next46.P15 (HasDirectionalDerivative directionalDerivative)

attribute [local instance] Classical.propDecidable

universe u v w

section Manifolds

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

variable [LocallyConvexSpace ℝ E] [T2Space E] [T2Space M]

/-- Theorem 2.6, PDF pp. 8--9: the maximal integral-curve construction
has an open domain, is jointly smooth, and is the unique flow on this
constructed domain with velocity X. Smaller flow restrictions are allowed. -/
theorem maximalFlow_exists_unique
    (hAtlas : BastianiAtlas (E := E) (M := M))
    (X : CoordinateField E M) (hX : IsLocallyIntegrable X) :
    IsLocalFlow (E := E) (maximalFlow X) ∧ HasVelocityField (maximalFlow X) X ∧
      ∀ P : FlowData M, IsLocalFlow (E := E) P → HasVelocityField P X →
        P.domain = (maximalFlow X).domain →
        ∀ t m, (t, m) ∈ P.domain → P.value t m = (maximalFlow X).value t m := by sorry

end Manifolds

end QAlgorithms.Papers.Independent.Intakenext100.P21
