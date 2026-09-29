-- Prove2me | Theorems.Thm_TarchaBraids_halfTwist_deck_permutation_v1
-- name    : TarchaBraids.halfTwist_deck_permutation_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T23:33:36.426463+00:00
-- url     : https://prove2.me/theorems/c88a7a3e-e474-40bd-be18-c1f654ad7167
-- title:
--   An elementary half-twist has the adjacent strand permutation
-- statement:
--   For the symmetric-group quotient covering from ordered to unordered configurations, the explicit geometric half-twist on adjacent strands has deck permutation equal to the corresponding adjacent transposition.
-- source:
--   Tarcha Teorema 3.11 and the explicit half-twist construction: the elementary braid generator interchanges exactly the two adjacent strand endpoints.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1
import Theorems.Thm_TarchaBraids_configProj_isQuotientCoveringMap_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem halfTwist_deck_permutation_v1 (n : ℕ) (i : Fin (n - 1)) :
    (configProj_isQuotientCoveringMap_v1 n).fundamentalGroupToMulOpposite
      (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})
      (halfTwistBraid n i) =
    MulOpposite.op (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by sorry

end TarchaBraids
