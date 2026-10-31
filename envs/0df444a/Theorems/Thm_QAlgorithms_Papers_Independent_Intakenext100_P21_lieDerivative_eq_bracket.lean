-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P21_lieDerivative_eq_bracket
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P21.lieDerivative_eq_bracket
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:46:28.068746+00:00
-- url     : https://prove2.me/theorems/20769069-8645-4111-ace7-f96291883f43
-- title:
--   The flow Lie derivative equals the vector-field bracket
-- statement:
--   Let $M$ be a Hausdorff smooth manifold modeled on a Hausdorff locally convex real space, with smoothness understood in the Bastiani calculus. Let $X$ be locally integrable, let $\Phi^X$ be its maximal local flow, and let $Y$ be any smooth vector field. Then
--
--   $$
--   \left.\frac{d}{dt}\right|_{t=0}(\Phi^X_{-t})_*Y=[X,Y].
--   $$
--
--   Here pushforward uses the differential of $\Phi^X_{-t}$, and its domain is $M_t=\{m:(t,m)\in D_X\}$. In local coordinates the bracket is $dY(X)-dX(Y)$.
--
--   This identifies the geometric derivative with the intrinsic Lie algebra bracket. The formal statement asserts existence of this derivative and its coordinate value in every chart.
-- source:
--   Integrability of unitary representations on reproducing kernel spaces, arXiv:1406.2681v3, PDF p. 10, Theorem 3.1

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

/-- Theorem 3.1, PDF pp. 10--11: the derivative at t=0 of
(Phi[-t])_*Y exists in every chart and equals dY(X)-dX(Y).
This is the intrinsic equality L_X Y=[X,Y] in coordinates. Local
integrability of X is retained from the section's preamble. -/
theorem lieDerivative_eq_bracket
    (hAtlas : BastianiAtlas (E := E) (M := M))
    (X Y : CoordinateField E M) (hX : IsLocallyIntegrable X)
    (hY : IsSmoothVectorField Y) :
    ∀ c ∈ atlas E M, ∀ m ∈ c.source,
      HasTimeDerivative (fun t => pullbackCoordinate (maximalFlow X) Y t c m) 0
        (bracketCoordinate X Y c m) := by sorry

end Manifolds

end QAlgorithms.Papers.Independent.Intakenext100.P21
