-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_raw_owner_weight_bound
-- name    : ThreeSum.RawIncidences.raw_owner_weight_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:48.564642+00:00
-- url     : https://prove2.me/theorems/2314f9dc-83fd-4b92-a461-1faf2b65937c
-- title:
--   Raw Incidences: raw owner weight bound
-- statement:
--   The Raw Incidences construction uses the raw owner weight bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L308-L317
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L308-L317

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

theorem ThreeSum.RawIncidences.raw_owner_weight_bound {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) (t : Original α β γ) :
    Arithmetic.fiberWeight (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t ≤
      representationCap h J := by sorry
