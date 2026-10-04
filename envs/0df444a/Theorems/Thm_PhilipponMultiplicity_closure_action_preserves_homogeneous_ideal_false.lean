-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_preserves_homogeneous_ideal_false
-- name    : PhilipponMultiplicity.closure_action_preserves_homogeneous_ideal_false
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T00:56:48.262981+00:00
-- url     : https://prove2.me/theorems/b7ce1392-029b-4e1c-8d55-c77605f11a3d
-- title:
--   Closure action preserves homogeneous ideal is false
-- statement:
--   Negation of PhilipponMultiplicity.closure_action_preserves_homogeneous_ideal (682402e1): the biconditional claiming that, for any group action τ on the projective closure, P lies in the vanishing ideal of the τ-translate of V if and only if P is the τ-translate of some Q in the vanishing ideal of V, is FALSE.
--
--   Counterexample (formalized in .work_disproof_closure/disproof_full.lean): take G = singleGroupProduct of the singleton embedded commutative group {[1:1]} in ℙ¹ ℂ, τ = the identity family, V = univ, P = X₀₀² − λ·X₀₀ with λ = pt.rep 0 ≠ 0, and Q = 0. The right-hand side holds with Q = 0 (τ is the identity and P vanishes at the single closure point s0), but P ∉ G.ambient.vanishingIdeal (Subtype.val '' V): P is not in the span of homogeneous polynomials vanishing on the point, by the diagonal-homomorphism argument (ψ kills every homogeneous generator but ψ(P) = t² ≠ 0). Hence the ↔ fails.
-- source:
--   Disproof of PhilipponMultiplicity.closure_action_preserves_homogeneous_ideal (682402e1), singleton-closure counterexample; full proof in .work_disproof_closure/disproof_full.lean. Cf. P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986).

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport

set_option autoImplicit false

namespace PhilipponMultiplicity

theorem closure_action_preserves_homogeneous_ideal_false :
    ¬ ∀ (K : Type) [NontriviallyNormedField K]
        (hK : IsPhilipponBaseField K)
        (G : EmbeddedGroupProduct K)
        (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
        (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
          (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
        (V : Set (groupProjectiveClosure G))
        (g : G.Point)
        (P : G.CoordinateRing),
        P ∈ G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)) ↔
          ∃ Q ∈ G.ambient.vanishingIdeal (Subtype.val '' V),
            ∀ x : groupProjectiveClosure G,
              G.ambient.eval P ((τ g x).val) = G.ambient.eval Q x.val  := by sorry

end PhilipponMultiplicity
