-- Prove2me | Theorems.Thm_TarchaBraids_braidWord_free_eval_v1
-- name    : TarchaBraids.braidWord_free_eval_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T19:57:08.244193+00:00
-- url     : https://prove2.me/theorems/46bddad7-ee57-469f-a81e-f32d395089ac
-- title:
--   A signed half-twist word evaluates to its concatenated geometric loop
-- statement:
--   For every finite signed word in the adjacent Artin generators, evaluating the word in the free group and then sending each generator to the corresponding elementary half-twist gives exactly the fundamental-group class of the concatenated positive and negative half-twist loops. The path concatenation order follows the pinned convention for the fundamental group multiplication.
-- source:
--   Algebraic/path bookkeeping for Tarcha Teorema 3.11, using the signed braid-word data and the pinned reversed path-concatenation convention.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem braidWord_free_eval_v1 :
    ∀ {n : ℕ} (w : List (BraidLetter n)),
      FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) (braidWordFree w) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (braidWordLoop n w)) := by sorry

end TarchaBraids
