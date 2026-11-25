-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_dg_br
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.dg_br
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:36.65835+00:00
-- url     : https://prove2.me/theorems/22dd2d91-bbac-56a9-8c76-82727fc70777
-- title:
--   Cayley Transform Darboux: dg br
-- statement:
--   The Cayley Transform Darboux construction uses the dg br property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L175-L184

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
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKG.CayleyTransformDarboux.dg_br (h : I → ℝ) (w : ι) (a b : I) : dg ι h * un w a b - un w a b * dg ι h = ((h a - h b : ℝ) : ℂ) • un w a b := by sorry
