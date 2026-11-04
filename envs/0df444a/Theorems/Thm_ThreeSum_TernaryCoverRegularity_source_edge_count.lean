-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_edge_count
-- name    : ThreeSum.TernaryCoverRegularity.source_edge_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:16.13048+00:00
-- url     : https://prove2.me/theorems/bc88d273-9895-4d2a-bbae-28ae8b7b9b05
-- title:
--   Ternary Cover Regularity: source edge count
-- statement:
--   Regularity gives the exact edge count without a multinomial formula.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L106-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L106-L123

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.source_edge_count {α π : DigitType} {a : TritWord L} (ha : HasType a α) :
    Fintype.card (LocalEdge L α π) =
      (vertices L α).card * Fintype.card (sourceFiber α π a) := by sorry
