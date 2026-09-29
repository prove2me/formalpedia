-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_half_twists_far_commute_v1
-- name    : TarchaBraids.thm_3_15_half_twists_far_commute_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T07:02:57.147997+00:00
-- url     : https://prove2.me/theorems/cb4f2526-6333-4a80-8b65-5c5afd1014a5
-- title:
--   Tarcha 3.15: far half-twists commute
-- statement:
--   For the standard geometric half-twist generators of the n-strand braid group, half-twists with generator indices at distance at least two commute. This is the far-commutativity relation used in the Artin presentation.
-- source:
--   Source-faithful child of TarchaBraids.thm_3_15_half_twists_satisfy_relations, corresponding to the non-adjacent half-twist relation in Tarcha's Teorema 3.15.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_half_twists_far_commute_v1 (n : ℕ) :
    ∀ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs →
      halfTwistBraid n i * halfTwistBraid n j =
        halfTwistBraid n j * halfTwistBraid n i := by sorry

end TarchaBraids
