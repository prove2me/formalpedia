-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_raw_true_triple_complete
-- name    : ThreeSum.RawIncidences.raw_true_triple_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:06.525678+00:00
-- url     : https://prove2.me/theorems/2135beae-3dc5-4011-9018-0e772acd5975
-- title:
--   Raw Incidences: raw true triple complete
-- statement:
--   The Raw Incidences construction uses the raw true triple complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L285-L289
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L285-L289

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

theorem ThreeSum.RawIncidences.raw_true_triple_complete {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {t : Original α β γ}
    (hh : 0 < h) (hP : 0 < P) (ht : t ∈ T) (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t := by sorry
