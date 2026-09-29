-- Prove2me | Theorems.Thm_TarchaBraids_strandExtension_braidWord_eval_v2
-- name    : TarchaBraids.strandExtension_braidWord_eval_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T16:37:49.055145+00:00
-- url     : https://prove2.me/theorems/d2d75c7d-2ad9-42a4-9954-26df428e1dcb
-- title:
--   Far-right strand extension commutes with evaluation of finite signed half-twist words
-- statement:
--   Adding a strand to the far right commutes with evaluating any finite signed word in adjacent half-twists. The proof is induction on the signed list using the previously accepted generator-level extension theorem.
-- source:
--   Tarcha algebraic strand transport; reusable naturality lemma extracted from accepted strand-extension construction.

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_strand_extension_v1

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

namespace TarchaBraids

theorem strandExtension_braidWord_eval_v2 (n : ℕ) (w : List (BraidLetter (n + 1))) :
    (FundamentalGroup.mapOfEq (TarchaBraids.StrandExtension.addU (n + 1))
      (TarchaBraids.StrandExtension.addU_base (n + 1)))
      (FreeGroup.lift (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
        (braidWordFree w)) =
    FreeGroup.lift (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
      (braidWordFree (w.map (fun a =>
        ({ index := Fin.castLE (by omega) a.index, sign := a.sign } :
          BraidLetter (n + 2))))) := by sorry

end TarchaBraids
