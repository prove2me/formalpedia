-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_preserves_homogeneous_ideal
-- name    : PhilipponMultiplicity.closure_action_preserves_homogeneous_ideal
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-02T08:25:08.486637+00:00
-- url     : https://prove2.me/theorems/682402e1-74ab-4a98-8de7-5c66bea63613
-- title:
--   Closure action transports homogeneous vanishing ideals
-- statement:
--   Decomposition child of PhilipponMultiplicity.connected_closure_action_degree_invariance: the equivariance of homogeneous vanishing ideals under the coherent closure action.
--
--   Let K be a Philippon base field, G an embedded product of commutative algebraic groups, and τ_g : X → X a coherent family of regular automorphisms of the projective closure X extending the group translations. For a closed locus V ⊆ X and g ∈ G(K), a coordinate polynomial P vanishes on the transported locus τ_g(V) if and only if P is the pullback along τ_g of a polynomial Q vanishing on V, i.e. eval P (τ_g(x)) = eval Q (x) for every closure point x. In ideal language, I(τ_g(V)) = τ_g·I(V) as multigraded ideals.
--
--   The forward direction is the content: regularity of τ_g guarantees the pullback of a polynomial is again a polynomial, landing in I(V); the converse is definitional. This isolates the equivariance step needed for the parent's degree invariance H(V;D) = H(τ_g(V);D) (Moreau's remark, Philippon 1986 pp. 375-376). The parent sketch (hilbertDegreeForm_eq_of_extendable_translations) already establishes uniqueness, identity, composition and inverse-regularity of the extensions; this node is the one remaining ideal-transport input.
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), 355-383; Moreau's remark pp. 375-376 (invariance of the degree under the coherent regular action extending translations). Auxiliary equivariance step: the action transports homogeneous vanishing ideals, I(τ_g(V)) = τ_g·I(V).

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false

namespace PhilipponMultiplicity

/-- **Closure action transports homogeneous vanishing ideals.** Let `τ` be a
coherent family of regular automorphisms of the projective closure extending
the group translations (`τ 0 = id`, `τ (g+h) = τ g ∘ τ h`, each `τ g`
regular). For a closed locus `V` and `g : G.Point`, a coordinate polynomial
`P` vanishes on the transported locus `τ g '' V` if and only if `P` is the
pullback along `τ g` of a polynomial `Q` vanishing on `V`:
`eval P (τ g x) = eval Q x` for all closure points `x`. In ideal language,
`I(τ g '' V) = τ g ⬝ I(V)` as multigraded ideals — the equivariance step used
to prove degree invariance `H(V;D) = H(τ g '' V;D)` in
`connected_closure_action_degree_invariance`. -/
theorem closure_action_preserves_homogeneous_ideal
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (V : Set (groupProjectiveClosure G))
    (g : G.Point)
    (P : G.CoordinateRing) :
    P ∈ G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)) ↔
      ∃ Q ∈ G.ambient.vanishingIdeal (Subtype.val '' V),
        ∀ x : groupProjectiveClosure G,
          G.ambient.eval P ((τ g x).val) = G.ambient.eval Q x.val := by sorry

end PhilipponMultiplicity
