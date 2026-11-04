-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_ofFn_tupleOfList
-- name    : ThreeSum.RawIncidences.ofFn_tupleOfList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:52.997445+00:00
-- url     : https://prove2.me/theorems/aaa75734-6961-43f1-844d-093b82cd6494
-- title:
--   Raw Incidences: of Fn tuple Of List
-- statement:
--   The Raw Incidences construction uses the of Fn tuple Of List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L114-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L114-L117

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

theorem ThreeSum.RawIncidences.ofFn_tupleOfList {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    List.ofFn (tupleOfList xs hlen) = xs := by sorry
