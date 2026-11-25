-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_dg_eq
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.dg_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:27.289192+00:00
-- url     : https://prove2.me/theorems/d75c5895-0c8f-489f-8443-007abe895526
-- title:
--   Cayley Transform Darboux: dg eq
-- statement:
--   The Cayley Transform Darboux construction uses the dg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L186-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L186-L189

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.dg_eq (h : I → ℝ) : dg ι h = ∑ w, ∑ a, (h a : ℂ) • un w a a := by sorry
