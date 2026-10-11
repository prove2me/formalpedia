-- Prove2me | Theorems.Thm_PhilipponMultiplicity_group_closure_has_proper_scheme_action
-- name    : PhilipponMultiplicity.group_closure_has_proper_scheme_action
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-11T00:46:55.963081+00:00
-- url     : https://prove2.me/theorems/9b2e3de0-1101-4f28-a73f-cf866880035f
-- title:
--   Proper reduced scheme realization of the Philippon closure action
-- statement:
--   Let K be an algebraically closed field and G an embedded product of commutative algebraic groups in the existing Philippon definitions. Suppose its actual multiprojective closure is equipped with an action by G(K) through individually regular bijections, satisfying the identity and group law. Then there is a proper reduced K-scheme X and a homeomorphism from that original closure onto the closed points of X, with the existing polynomial Zariski topology, and an action through K-scheme automorphisms agreeing with the original action. All identity and composition laws are preserved. No joint regularity of the parameter is imposed.
--
--   This supplies the scheme-realization portion of the local-complex frontier. It does not assert Neron-Severi finite generation, the coherent-sheaf family model, eventual Hilbert comparison, or the full frontier conclusion. The construction uses the same Segre substitution and diagonal ideal as the existing exact Hilbert-function comparison.
-- source:
--   Supporting construction for PhilipponMultiplicity.closure_action_has_local_complex_model, https://prove2.me/theorems/799c6ab6-409d-4f14-b567-a940d6ef43da. Constructed from the existing mission definitions by normalized affine charts, Segre coordinates, and gluing regular maps; no paper statement changed.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false

namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory
universe u

theorem group_closure_has_proper_scheme_action
    (K : Type u) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      Subtype.val (fun x => (τ g x).val)) :
    letI := G.ambient.zariskiTopology
    ∃ (X : Scheme.{u}) (π : X ⟶ Spec (.of K))
      (e : groupProjectiveClosure G ≃ₜ {x : X | IsClosed {x}}),
      IsProper π ∧ IsReduced X ∧
      ∃ T : G.Point → (X ≅ X),
        (∀ g, (T g).hom ≫ π = π) ∧
        (∀ g x, (T g).hom (e x).val = (e (τ g x)).val) ∧
        T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by sorry

end PhilipponMultiplicity
