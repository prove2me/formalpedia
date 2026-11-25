-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_Lie_comm
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.Lie.comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:39:14.564397+00:00
-- url     : https://prove2.me/theorems/245777c4-42c3-54fc-b62c-ae4a33f73d86
-- title:
--   Lie: comm
-- statement:
--   The Lie construction uses the comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L17-L21

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKG.CayleyTransformDarboux.Lie.comm {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) (X Y : A) (x : M) :
    act X (act Y x) = act Y (act X x) + act (X * Y - Y * X) x := by sorry
