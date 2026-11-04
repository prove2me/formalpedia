-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_tupleKey_eq
-- name    : ThreeSum.RawIncidences.tupleKey_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:04.435204+00:00
-- url     : https://prove2.me/theorems/c57973e9-43ce-47e3-8a51-2011d344a4b2
-- title:
--   Raw Incidences: tuple Key eq
-- statement:
--   The Raw Incidences construction uses the tuple Key eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L60-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L60-L64

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

theorem ThreeSum.RawIncidences.tupleKey_eq {h J : ℕ} (t : ChoiceTuple h J) :
    tupleKey t = tupleRight t - tupleLeft t := by sorry
