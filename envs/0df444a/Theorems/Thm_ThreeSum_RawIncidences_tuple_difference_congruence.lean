-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_tuple_difference_congruence
-- name    : ThreeSum.RawIncidences.tuple_difference_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:49.458536+00:00
-- url     : https://prove2.me/theorems/93b95841-63d7-41ca-ad00-7af81b41f6f9
-- title:
--   Raw Incidences: tuple difference congruence
-- statement:
--   The Raw Incidences construction uses the tuple difference congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L125-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L125-L131

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

theorem ThreeSum.RawIncidences.tuple_difference_congruence {h J : ℕ} {t : ChoiceTuple h J} {b c : ℤ}
    (ht : List.ofFn t ∈ representations h J b c) :
    globalModulus h J ∣ (c - b) - tupleKey t := by sorry
