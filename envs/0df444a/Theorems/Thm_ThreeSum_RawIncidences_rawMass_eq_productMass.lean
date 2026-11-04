-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_rawMass_eq_productMass
-- name    : ThreeSum.RawIncidences.rawMass_eq_productMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:53.825895+00:00
-- url     : https://prove2.me/theorems/8ed50db4-7e92-444d-b1f7-efefdbdc1fb4
-- title:
--   Raw Incidences: raw Mass eq product Mass
-- statement:
--   Exact expansion of all bucket products into original-index incidences.
--   No bucket-uniformity or multiplicity hypothesis is used.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L381-L398
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L381-L398

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

theorem ThreeSum.RawIncidences.rawMass_eq_productMass (h J : ℕ) (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    rawMass h J P d (A ×ˢ (B ×ˢ C)) a b c = productMass h J P d A B C a b c := by sorry
