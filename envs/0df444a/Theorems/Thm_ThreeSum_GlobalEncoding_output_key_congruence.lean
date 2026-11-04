-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_output_key_congruence
-- name    : ThreeSum.GlobalEncoding.output_key_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:50.52416+00:00
-- url     : https://prove2.me/theorems/88ef71ae-3be9-4972-9826-5c62b3294580
-- title:
--   Global Encoding: output key congruence
-- statement:
--   The Global Encoding construction uses the output key congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L279-L291
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L279-L291

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

theorem ThreeSum.GlobalEncoding.output_key_congruence {h J : ℕ} {a b : ℤ}
    {xs : List (RetainedChoice h)} (hxs : xs ∈ representations h J a b) :
    globalModulus h J ∣ (b - a) -
      globalKey (outputOfChoices xs ((mem_representations h J a b xs).mp hxs).1) := by sorry
