-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_rawMass_eq_sum_witnesses
-- name    : ThreeSum.RawIncidences.rawMass_eq_sum_witnesses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:15:04.973202+00:00
-- url     : https://prove2.me/theorems/97af9c71-84f2-4431-9d3c-f16fb8cce0a2
-- title:
--   Raw Incidences: raw Mass eq sum witnesses
-- statement:
--   The Raw Incidences construction uses the raw Mass eq sum witnesses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L322-L326
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L322-L326

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

theorem ThreeSum.RawIncidences.rawMass_eq_sum_witnesses (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    rawMass h J P d T a b c =
      ∑ t ∈ T, (witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card := by sorry
