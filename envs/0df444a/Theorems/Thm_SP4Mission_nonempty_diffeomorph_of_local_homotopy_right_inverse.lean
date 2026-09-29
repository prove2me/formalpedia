-- Prove2me | Theorems.Thm_SP4Mission_nonempty_diffeomorph_of_local_homotopy_right_inverse
-- name    : SP4Mission.nonempty_diffeomorph_of_local_homotopy_right_inverse
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-06T09:33:55.556595+00:00
-- url     : https://prove2.me/theorems/0f57ba3c-37cf-47b2-81cd-dc39db51d897
-- title:
--   Compact local diffeomorphism with a homotopy right inverse
-- statement:
--   Let X be a compact connected Hausdorff smooth real d-manifold and let Y be a nonempty Hausdorff smooth real d-manifold, with their given smooth atlases. Suppose a continuous map f from X to Y is a smooth local diffeomorphism and admits a continuous map g from Y to X satisfying
--
--   $$f \circ g \simeq \operatorname{id}_Y.$$
--
--   Then
--
--   $$\operatorname{Diffeomorph}(X,Y) \ne \varnothing.$$
--
--   This local-to-global criterion is a supporting result for the smooth four-dimensional Poincare mission. It supplies the global diffeomorphism once an appropriate local diffeomorphism and homotopy right inverse have been constructed. It is a corollary of standard covering-space theory, valid in every finite dimension.
--
--   **Formalization Note** The source is assumed preconnected in Lean; its nonemptiness follows from the map g and the nonempty target. No simple-connectedness assumption or left-inverse homotopy is needed.
-- source:
--   Derived supporting result for Prove2Me SP4Mission.smooth_poincare_4 (acb88840-8df8-4040-89df-f387272d80a9). Hatcher, Algebraic Topology, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, Propositions 1.30 and 1.34, printed pp. 60 and 62; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Topology/Covering/Basic.lean, isLocalHomeomorph_iff_isCoveringMap, and Geometry/Manifold/LocalDiffeomorph.lean, IsLocalDiffeomorph.diffeomorphOfBijective. The displayed statement is a corollary derived from these results, not a quotation.

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open ContinuousMap

theorem SP4Mission.nonempty_diffeomorph_of_local_homotopy_right_inverse
    {d : ℕ}
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X]
    [PreconnectedSpace X] [Nonempty Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) Y]
    [IsManifold (𝓡 d) ∞ X] [IsManifold (𝓡 d) ∞ Y]
    (f : C(X, Y)) (hf : IsLocalDiffeomorph (𝓡 d) (𝓡 d) ∞ f)
    (g : C(Y, X)) (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) :
    Nonempty (X ≃ₘ⟮𝓡 d, 𝓡 d⟯ Y) := by sorry
