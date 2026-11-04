-- Prove2me | Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
-- name    : P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:20.315614+00:00
-- url     : https://prove2.me/theorems/76e23df2-745c-4a19-a432-94a4094fb73d
-- title:
--   P2 M Three Sum Ternary Cover Regularity map Edge symm  4d2d267acd4d: P2 M Three Sum Ternary Cover Regularity map Edge symm  4d2d267acd4d
-- statement:
--   The P2 M Three Sum Ternary Cover Regularity map Edge symm  4d2d267acd4d construction uses the P2 M Three Sum Ternary Cover Regularity map Edge symm  4d2d267acd4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L70-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L70-L73

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : mapEdge σ (mapEdge σ.symm e) = e := by sorry

alias «ThreeSum».«TernaryCoverRegularity».«mapEdge_symm'» := P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
