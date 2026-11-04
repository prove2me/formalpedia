-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_tuple_mem_representations
-- name    : ThreeSum.RawIncidences.tuple_mem_representations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:24.305051+00:00
-- url     : https://prove2.me/theorems/c0e3f8c5-7bbb-4642-b1a6-ee17647a15b3
-- title:
--   Raw Incidences: tuple mem representations
-- statement:
--   The Raw Incidences construction uses the tuple mem representations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L119-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L119-L123

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds

theorem ThreeSum.RawIncidences.tuple_mem_representations {h J : ℕ} (t : ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ representations h J b c ↔
      globalModulus h J ∣ b - tupleLeft t ∧ globalModulus h J ∣ c - tupleRight t := by sorry
