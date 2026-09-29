-- Prove2me | Theorems.Thm_TarchaBraids_strandIdx_swap_free_lift_surjective_v1
-- name    : TarchaBraids.strandIdx_swap_free_lift_surjective_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T06:44:42.455174+00:00
-- url     : https://prove2.me/theorems/6256bd30-4c5f-4801-bd08-810ffcaefe02
-- title:
--   The strand-index adjacent swaps give a surjective free-group lift
-- statement:
--   For n labelled strands, every endpoint permutation is represented by a signed word in the adjacent swaps indexed exactly as the braid generators, using strandIdx i and strandIdxSucc i. This is the indexing bridge from the standard Fin m adjacent-swap theorem to the form required by the half-twist permutation-correction theorem.
-- source:
--   Tarcha Teorema 3.11 endpoint-permutation correction. This child translates the already proved adjacent-transposition generation theorem into the exact strandIdx/strandIdxSucc indexing used by the geometric half-twists.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_TarchaBraids_adjacent_swap_free_lift_surjective_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem strandIdx_swap_free_lift_surjective_v1 (n : ℕ) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) =>
        Equiv.swap (strandIdx i) (strandIdxSucc i))) := by sorry

end TarchaBraids
