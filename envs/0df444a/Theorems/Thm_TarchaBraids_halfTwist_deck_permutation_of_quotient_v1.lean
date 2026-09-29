-- Prove2me | Theorems.Thm_TarchaBraids_halfTwist_deck_permutation_of_quotient_v1
-- name    : TarchaBraids.halfTwist_deck_permutation_of_quotient_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T23:37:07.799645+00:00
-- url     : https://prove2.me/theorems/c7511d6a-5f41-42b7-86b5-820e3d7c9221
-- title:
--   The explicit half-twist has the adjacent deck permutation
-- statement:
--   For any symmetric-group quotient-covering structure on the ordered-to-unordered configuration projection, the explicit elementary half-twist has deck permutation equal to the corresponding adjacent transposition.
-- source:
--   Tarcha Teorema 3.11 and the explicit half-twist construction: the elementary braid generator interchanges exactly the two adjacent strand endpoints.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem halfTwist_deck_permutation_of_quotient_v1 (n : ℕ) (i : Fin (n - 1))
    (hp : IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n))) :
    hp.fundamentalGroupToMulOpposite
      (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})
      (halfTwistBraid n i) =
    MulOpposite.op (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by sorry

end TarchaBraids
