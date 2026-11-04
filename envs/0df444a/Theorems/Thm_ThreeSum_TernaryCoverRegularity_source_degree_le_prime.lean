-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_degree_le_prime
-- name    : ThreeSum.TernaryCoverRegularity.source_degree_le_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:10.334003+00:00
-- url     : https://prove2.me/theorems/566f3adf-09ad-4414-9cad-4fc2c463b82f
-- title:
--   Ternary Cover Regularity: source degree le prime
-- statement:
--   The Ternary Cover Regularity construction uses the source degree le prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L131-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L131-L135

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.source_degree_le_prime {α π : DigitType} {a : TritWord L} (ha : HasType a α)
    (P : ℕ) (hE : Fintype.card (LocalEdge L α π) ≤ P^2) :
    Fintype.card (sourceFiber α π a) ≤ P := by sorry
