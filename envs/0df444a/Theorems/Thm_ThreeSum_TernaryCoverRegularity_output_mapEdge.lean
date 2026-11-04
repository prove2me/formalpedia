-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
-- name    : ThreeSum.TernaryCoverRegularity.output_mapEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:15.95224+00:00
-- url     : https://prove2.me/theorems/e212f8f7-20da-40ce-b2bf-96648addd599
-- title:
--   Ternary Cover Regularity: output map Edge
-- statement:
--   The Ternary Cover Regularity construction uses the output map Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L52-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L52-L53

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.output_mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : output (mapEdge σ e) = reindex σ (output e) := by sorry

attribute [defeq] ThreeSum.TernaryCoverRegularity.output_mapEdge
