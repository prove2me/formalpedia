-- Prove2me | Theorems.Thm_SmoothJetExtension_moving_circle_first_jet_extension
-- name    : SmoothJetExtension.moving_circle_first_jet_extension
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T20:51:54.227466+00:00
-- url     : https://prove2.me/theorems/b9644b2b-43ba-4571-b8a4-bb0cbf133c16
-- title:
--   Compact smooth first-jet extension along a moving embedded circle
-- statement:
--   Let k(t,u) be a globally smooth family of curves in real four-space, with u on the unit circle and time t in [0,1]. Suppose the worldsheet map F(t,u)=(t,k(t,u)) is injective on that compact cylinder and each circle derivative of k is nonzero. Let h(t,u) be a smooth scalar value function and let L(t,u) be a family of ambient covectors on time times four-space, smooth on an open neighborhood of the cylinder. Assume their tangential compatibility:
--
--   $$Dh_{(t,u)}(a,bJu)=L_{(t,u)}\bigl(a,Dk_{(t,u)}(a,bJu)\bigr).$$
--
--   Then there is a globally smooth compactly supported scalar H on time times four-space such that, throughout the cylinder,
--
--   $$H(F(t,u))=h(t,u),\qquad DH(F(t,u))=L(t,u).$$
--
--   Here Ju is the counterclockwise unit-circle tangent. This is a parametric first-jet extension along an embedded worldsheet; it supplies the scalar Hamiltonian extension needed for contact isotopy generation.
-- source:
--   Derived first-jet extension lemma for Geiges Contact Geometry, arXiv:math/0307242v2, affine normal extension construction pp.32–33 and contact submanifold isotopy extension Theorem2.42 pp.34–36. The formal proof derives local retractions from the inverse-function theorem and compact injectivity, then applies the proved compact_first_jet_extension. This is a derived supporting theorem for https://prove2.me/theorems/127b6bf7-3a22-4600-82ae-2c5c3205a1bb, not a verbatim numbered statement.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set Function
open scoped ContDiff

theorem SmoothJetExtension.moving_circle_first_jet_extension
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hinj : InjOn ((fun p : ℝ × Plane => (p.1, k p))) (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle))
    (hreg : ∀ p ∈ (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0, circleTangent p.2) ≠ 0)
    (h : ℝ × Plane → ℝ) (hh : ContDiff ℝ ∞ h)
    (L : ℝ × Plane → ((ℝ × Phase) →L[ℝ] ℝ))
    (P : Set (ℝ × Plane)) (hPo : IsOpen P) (hAP : (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle) ⊆ P)
    (hL : ContDiffOn ℝ ∞ L P)
    (hcomp : ∀ p ∈ (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle), ∀ a b : ℝ,
      fderiv ℝ h p (a, b • circleTangent p.2) =
        L p (a, fderiv ℝ k p (a, b • circleTangent p.2))) :
    ∃ H : ℝ × Phase → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ p ∈ (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle), H ((fun p : ℝ × Plane => (p.1, k p)) p) = h p ∧ fderiv ℝ H ((fun p : ℝ × Plane => (p.1, k p)) p) = L p := by sorry
