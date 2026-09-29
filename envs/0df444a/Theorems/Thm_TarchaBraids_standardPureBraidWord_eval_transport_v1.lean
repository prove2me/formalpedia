-- Prove2me | Theorems.Thm_TarchaBraids_standardPureBraidWord_eval_transport_v1
-- name    : TarchaBraids.standardPureBraidWord_eval_transport_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T21:56:29.489181+00:00
-- url     : https://prove2.me/theorems/c1c76a77-22a7-459a-9d60-8a4dc292149c
-- title:
--   Classical pure-braid evaluation commutes with far-right strand transport up to conjugation
-- statement:
--   The evaluated classical pure-braid word on n+2 strands is the last elementary half-twist conjugating the far-right extension of the old evaluated word.
-- source:
--   Tarcha Theorem 3.11; consequence of the accepted finite signed-list transport identity and the accepted naturality of half-twist-word evaluation.

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Definitions.Def_TarchaBraids_strand_extension_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_list_transport_v1
import Theorems.Thm_TarchaBraids_strandExtension_braidWord_eval_v2

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

namespace TarchaBraids

theorem standardPureBraidWord_eval_transport_v1 (n : ℕ) (j : Fin n) :
    FreeGroup.lift
        (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
        (braidWordFree (standardPureBraidWord (n + 1) j.castSucc))
      =
    halfTwistBraid (n + 2) (Fin.last n) *
      (FundamentalGroup.mapOfEq (addU (n + 1)) (addU_base (n + 1)))
        (FreeGroup.lift
          (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
          (braidWordFree (standardPureBraidWord n j))) *
      (halfTwistBraid (n + 2) (Fin.last n))⁻¹ := by sorry

end TarchaBraids
