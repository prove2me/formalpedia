-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverOutputCap_edges_card_le
-- name    : ThreeSum.TernaryCoverOutputCap.edges_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:56.322265+00:00
-- url     : https://prove2.me/theorems/aaaa3ba4-050c-4dfa-a752-b4e6b7419e57
-- title:
--   Ternary Cover Output Cap: edges card le
-- statement:
--   The Ternary Cover Output Cap construction uses the edges card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L68-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L68-L82

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverOutputCap.edges_card_le (α π : DigitType) :
    Fintype.card (LocalEdge L α π) ≤ (vertices L π).card * (2^(π 1)*3^(π 2)) := by sorry
