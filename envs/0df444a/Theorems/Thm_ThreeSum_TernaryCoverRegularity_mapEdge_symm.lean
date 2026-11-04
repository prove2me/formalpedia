-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
-- name    : ThreeSum.TernaryCoverRegularity.mapEdge_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:27.628701+00:00
-- url     : https://prove2.me/theorems/90548256-78e5-4cee-8876-f9f732ae2b8c
-- title:
--   Ternary Cover Regularity: map Edge symm
-- statement:
--   The Ternary Cover Regularity construction uses the map Edge symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L65-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L65-L68

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.mapEdge_symm (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : mapEdge σ.symm (mapEdge σ e) = e := by sorry
