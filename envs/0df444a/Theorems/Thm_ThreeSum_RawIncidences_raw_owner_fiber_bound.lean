-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_raw_owner_fiber_bound
-- name    : ThreeSum.RawIncidences.raw_owner_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:45.318838+00:00
-- url     : https://prove2.me/theorems/96dc8438-a2a6-44b9-a2b0-8c7aa04fbaaf
-- title:
--   Raw Incidences: raw owner fiber bound
-- statement:
--   The Raw Incidences construction uses the raw owner fiber bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L291-L306
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L291-L306

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

theorem ThreeSum.RawIncidences.raw_owner_fiber_bound {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) (t : Original α β γ) :
    ((rawOn h J P d T a b c).filter fun r => r.1 = t).card ≤ representationCap h J := by sorry
