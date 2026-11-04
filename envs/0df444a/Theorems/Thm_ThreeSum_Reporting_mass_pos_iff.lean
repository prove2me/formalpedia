-- Prove2me | Theorems.Thm_ThreeSum_Reporting_mass_pos_iff
-- name    : ThreeSum.Reporting.mass_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:34.16171+00:00
-- url     : https://prove2.me/theorems/509b7c51-f6ac-4426-a52f-617f4a041593
-- title:
--   Reporting: mass pos iff
-- statement:
--   The Reporting construction uses the mass pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Reporting.lean#L25-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Reporting.lean#L25-L36

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting
set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]

theorem ThreeSum.Reporting.mass_pos_iff (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) :
    0 < mass I word weight k pre ↔
      ∃ i ∈ I, (word i).take k = pre ∧ 0 < weight i := by sorry
