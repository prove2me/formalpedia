-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
-- name    : ThreeSum.TernaryCoverRegularity.right_mapEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:16.924262+00:00
-- url     : https://prove2.me/theorems/d61949d2-cb09-44be-ac41-1ebde1536e93
-- title:
--   Ternary Cover Regularity: right map Edge
-- statement:
--   The Ternary Cover Regularity construction uses the right map Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L49-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L49-L50

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.right_mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : right (mapEdge σ e) = reindex σ (right e) := by sorry

attribute [defeq] ThreeSum.TernaryCoverRegularity.right_mapEdge
