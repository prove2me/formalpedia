-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_half_twists_adjacent_braid_v1
-- name    : TarchaBraids.thm_3_15_half_twists_adjacent_braid_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T07:02:56.619992+00:00
-- url     : https://prove2.me/theorems/52db34c2-22ce-4c30-8f52-c620991328d5
-- title:
--   Tarcha 3.15: adjacent half-twists satisfy the braid relation
-- statement:
--   For the standard geometric half-twist generators of the n-strand braid group, adjacent generators satisfy the three-term braid relation. This is the local three-strand isotopy used in the Artin presentation.
-- source:
--   Source-faithful child of TarchaBraids.thm_3_15_half_twists_satisfy_relations, corresponding to the adjacent braid relation in Tarcha's Teorema 3.15.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_half_twists_adjacent_braid_v1 (n : ℕ) :
    ∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
      halfTwistBraid n i * halfTwistBraid n j * halfTwistBraid n i =
        halfTwistBraid n j * halfTwistBraid n i * halfTwistBraid n j := by sorry

end TarchaBraids
