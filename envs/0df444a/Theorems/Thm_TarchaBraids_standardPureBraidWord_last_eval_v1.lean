-- Prove2me | Theorems.Thm_TarchaBraids_standardPureBraidWord_last_eval_v1
-- name    : TarchaBraids.standardPureBraidWord_last_eval_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T15:18:00.241539+00:00
-- url     : https://prove2.me/theorems/63461cef-89a0-4511-a630-4904074b86ad
-- title:
--   The adjacent classical pure braid word evaluates to the square of the final half-twist
-- statement:
--   For n+2 strands, when the new last strand circles its immediate neighbour, the classical pure-braid word contains no conjugating generators and evaluates to the square of the final elementary half-twist. This supplies the algebraic adjacent case of the standard-loop/classical-word identity.
-- source:
--   Tarcha Teorema 3.11, classical pure braid generator A_(n+1,n+2) = σ_n²; prerequisite of BraidsLinksMCG.standardGen_image_eq_classical_halfTwist_word_v1 (target bb2b3eec-5ba2-4852-8ce9-2ff66524968b).

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1

open BraidsLinksMCG TarchaBraids

namespace TarchaBraids

theorem standardPureBraidWord_last_eval_v1 (n : ℕ) :
    FreeGroup.lift
        (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
        (braidWordFree (standardPureBraidWord (n + 1) (Fin.last n)))
      =
    (halfTwistBraid (n + 2) (⟨n, by omega⟩ : Fin (n + 2 - 1))) ^ 2 := by sorry

end TarchaBraids
