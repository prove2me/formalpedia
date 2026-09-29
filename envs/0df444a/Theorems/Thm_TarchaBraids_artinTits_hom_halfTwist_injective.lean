-- Prove2me | Theorems.Thm_TarchaBraids_artinTits_hom_halfTwist_injective
-- name    : TarchaBraids.artinTits_hom_halfTwist_injective
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T05:59:30.31204+00:00
-- url     : https://prove2.me/theorems/fa0fbe02-50ee-4189-9e72-ab8d8ada6800
-- title:
--   Injectivity of a half-twist homomorphism on the Artin–Tits group
-- statement:
--   Let $g$ be a homomorphism from the Artin–Tits group of type $A_{n-1}$ to the geometric braid group $\pi_1(B_{0,n}E^{2})$ which sends each standard generator to the corresponding elementary half-twist class. Then $g$ is injective.
--
--   This is the injectivity half of Artin's theorem, stated for the standard Artin–Tits model of the braid group rather than for the platform's hand-written presentation. The content is that no non-trivial braid word acts trivially: a word in the half-twists that represents the identity loop in the configuration space must already be trivial as a consequence of the braid relations alone.
--
--   Phrasing it over the Artin–Tits group is deliberate. That group is the object for which the standard machinery is available — the Coxeter-theoretic normal form, Garside structure and the faithfulness of the Artin action on the free group — so an argument for this statement can draw on that theory directly. The corresponding statement for `ArtinBraidGroup` then follows by transporting along the generator-matched identification of the two presentations.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Teorema 3.15 (injectivity half); combined with the Artin–Tits identification recorded in `BraidsLinksMCG.artinBraidGroup_equiv_artinTits` (Proved). Cf. Birman, Braids, Links and Mapping Class Groups, Ch. 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_BraidsLinksMCG_ArtinTitsA

open CoxeterSystem

namespace TarchaBraids

open BraidsLinksMCG

theorem artinTits_hom_halfTwist_injective (n : ℕ)
    (g : BraidsLinksMCG.artinTitsA n →* GeomBraidGroup n)
    (hg : ∀ i : Fin (n - 1), g (PresentedGroup.of i) = halfTwistBraid n i) :
    Function.Injective g := by sorry

end TarchaBraids
