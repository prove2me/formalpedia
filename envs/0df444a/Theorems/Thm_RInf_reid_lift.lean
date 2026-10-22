-- Prove2me | Theorems.Thm_RInf_reid_lift
-- name    : RInf.reid_lift
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:26:10.674707+00:00
-- url     : https://prove2.me/theorems/2e9301d1-d97a-4b28-8e0f-72f22084887a
-- title:
--   The Reidemeister number is monotone under surjection (Remark 1)
-- statement:
--   If a surjective homomorphism from G onto H intertwines the automorphism of G with the automorphism of H, and the Reidemeister number of the automorphism of H is infinite, then the Reidemeister number of the automorphism of G is infinite: twisted-conjugate elements of G map to twisted-conjugate elements of H, so an infinite sequence of pairwise non-twisted-conjugate elements of H lifts to a sequence of pairwise non-twisted-conjugate elements of G. This is the reduction of Remark 1 that carries infinitude from a quotient back to the group.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Section 2 (Remark 1).

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid

namespace RInf

/-!  Milestone 1 (Remark 1, after Lemma 2.2 of Dekimpe and Goncalves): the
Reidemeister number is monotone under surjection. If a surjective homomorphism
pi intertwines the automorphism α of G with the automorphism β of H, and the
Reidemeister number of β is infinite, then the Reidemeister number of α is
infinite: twisted-conjugate elements of G map to twisted-conjugate elements of
H, so infinitely many Reidemeister classes of H lift to pairwise distinct
classes of G. This is the reduction that carries infinitude from the
commutator layer quotient back to the braid group. -/
theorem reid_lift {G H : Type*} [Group G] [Group H]
    (pi : G →* H) (hsurj : ∀ y : H, ∃ x : G, pi x = y)
    (α : G ≃* G) (β : H ≃* H) (hcomm : ∀ x : G, pi (α x) = β (pi x))
    (hβ : ReidInf β.toMonoidHom) : ReidInf α.toMonoidHom := by sorry

end RInf
