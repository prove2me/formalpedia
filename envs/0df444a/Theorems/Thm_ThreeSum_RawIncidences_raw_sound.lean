-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_raw_sound
-- name    : ThreeSum.RawIncidences.raw_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:52.464852+00:00
-- url     : https://prove2.me/theorems/06e329d8-cb1e-403e-bffd-c1e5b58d2709
-- title:
--   Raw Incidences: raw sound
-- statement:
--   The Raw Incidences construction uses the raw sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L272-L276
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L272-L276

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
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.RawIncidences.raw_sound {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hr : r ∈ rawOn h J P d T a b c) : P ∣ difference a b c r.1 := by sorry
