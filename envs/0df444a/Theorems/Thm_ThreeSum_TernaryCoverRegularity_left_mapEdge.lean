-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
-- name    : ThreeSum.TernaryCoverRegularity.left_mapEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:16.029802+00:00
-- url     : https://prove2.me/theorems/5ef7b902-d60e-4881-b6bf-59b29d5b58fd
-- title:
--   Ternary Cover Regularity: left map Edge
-- statement:
--   The Ternary Cover Regularity construction uses the left map Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L46-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L46-L47

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.left_mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : left (mapEdge σ e) = reindex σ (left e) := by sorry

attribute [defeq] ThreeSum.TernaryCoverRegularity.left_mapEdge
