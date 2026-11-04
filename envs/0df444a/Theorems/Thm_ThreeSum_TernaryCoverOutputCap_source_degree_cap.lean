-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverOutputCap_source_degree_cap
-- name    : ThreeSum.TernaryCoverOutputCap.source_degree_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:18.118656+00:00
-- url     : https://prove2.me/theorems/07b83495-e627-4ed0-a5a7-0656c9850b01
-- title:
--   Ternary Cover Output Cap: source degree cap
-- statement:
--   The prime-size inequality alone now pays all source fibers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L85-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L85-L88

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverOutputCap.source_degree_cap {α π : DigitType} {a : TritWord L} (ha : HasType a α)
    (P : ℕ) (hP : (vertices L π).card * (2^(π 1)*3^(π 2)) ≤ P^2) :
    Fintype.card (TernaryCoverRegularity.sourceFiber α π a) ≤ P := by sorry
