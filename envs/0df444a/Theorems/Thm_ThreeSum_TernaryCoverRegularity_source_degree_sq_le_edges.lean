-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_degree_sq_le_edges
-- name    : ThreeSum.TernaryCoverRegularity.source_degree_sq_le_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:06.157082+00:00
-- url     : https://prove2.me/theorems/3848691d-3c75-4dad-bbc4-ca080b04697a
-- title:
--   Ternary Cover Regularity: source degree sq le edges
-- statement:
--   The full edge count pays every individual source-degree square.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L126-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L126-L129

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.source_degree_sq_le_edges {α π : DigitType} {a : TritWord L} (ha : HasType a α) :
    (Fintype.card (sourceFiber α π a))^2 ≤ Fintype.card (LocalEdge L α π) := by sorry
