-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_witnesses_nonempty_iff
-- name    : ThreeSum.RawIncidences.witnesses_nonempty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:44.596901+00:00
-- url     : https://prove2.me/theorems/2c3a00b7-814e-4adf-bf27-50c0d0514a36
-- title:
--   Raw Incidences: witnesses nonempty iff
-- statement:
--   The Raw Incidences construction uses the witnesses nonempty iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L184-L190
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L184-L190

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

theorem ThreeSum.RawIncidences.witnesses_nonempty_iff {h J : ℕ} {P d a b c : ℤ}
    (hh : 0 < h) (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).Nonempty ↔ P ∣ c - b - a := by sorry
