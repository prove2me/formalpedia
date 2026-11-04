-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_degree_le_vertices
-- name    : ThreeSum.TernaryCoverRegularity.source_degree_le_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:07.887768+00:00
-- url     : https://prove2.me/theorems/0e2c12c1-e7cf-4973-95e9-826ea652dcb9
-- title:
--   Ternary Cover Regularity: source degree le vertices
-- statement:
--   A source fiber injects into the other endpoint family.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L93-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L93-L103

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.source_degree_le_vertices (α π : DigitType) (a : TritWord L) :
    Fintype.card (sourceFiber α π a) ≤ (vertices L α).card := by sorry
