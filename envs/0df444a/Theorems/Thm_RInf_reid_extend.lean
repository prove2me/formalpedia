-- Prove2me | Theorems.Thm_RInf_reid_extend
-- name    : RInf.reid_extend
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:30:06.184866+00:00
-- url     : https://prove2.me/theorems/ce9f45ae-18a7-4033-8856-3fecabedfd24
-- title:
--   The Reidemeister number is monotone under extension by a normal invariant subgroup (Lemma 2.2)
-- statement:
--   If the group H embeds into G with normal image, the automorphism of H is the restriction of the automorphism of G, and the Reidemeister number of the automorphism of H is infinite, then the Reidemeister number of the automorphism of G is infinite. Together with the surjection monotonicity this is the abstract justification of the transfer design that carries infinitude from the commutator layer to the braid group.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 2 (Lemma 2.2 of Dekimpe and Goncalves).

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid

namespace RInf

/-!  Milestone 7 (Lemma 2.2 of Dekimpe and Goncalves): the Reidemeister
number is monotone under extension by a normal invariant subgroup. If H embeds
into G with normal image, the automorphism β of H is the restriction of the
automorphism α of G, and the Reidemeister number of β is infinite, then the
Reidemeister number of α is infinite. Together with milestone 1 this is the
abstract justification of the transfer design of the world, which carries the
infinitude from the commutator layer to the braid group. -/
theorem reid_extend {H G : Type*} [Group H] [Group G]
    (inj : H →* G) (hinj : ∀ x y : H, inj x = inj y → x = y)
    (hnorm : ∀ (g : G) (x : H), ∃ y : H, inj y = g * inj x * g⁻¹)
    (α : G ≃* G) (β : H ≃* H) (hcomm : ∀ x : H, inj (β x) = α (inj x))
    (hβ : ReidInf β.toMonoidHom) : ReidInf α.toMonoidHom := by sorry

end RInf
