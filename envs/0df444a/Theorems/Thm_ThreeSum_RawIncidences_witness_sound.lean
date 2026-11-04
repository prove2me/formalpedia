-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_witness_sound
-- name    : ThreeSum.RawIncidences.witness_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:19.956592+00:00
-- url     : https://prove2.me/theorems/8a6e2f6a-c67b-4f70-ac87-1f1063d6f13c
-- title:
--   Raw Incidences: witness sound
-- statement:
--   The Raw Incidences construction uses the witness sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L150-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L150-L159

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

theorem ThreeSum.RawIncidences.witness_sound {h J : ℕ} {P d a b c : ℤ} {w : Witness h J}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hw : w ∈ witnesses h J P d a b c) : P ∣ c - b - a := by sorry
