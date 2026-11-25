-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_dg_hw
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.dg_hw
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:47.386972+00:00
-- url     : https://prove2.me/theorems/b34996a9-e95a-5431-8db6-962e8ad82b1c
-- title:
--   Cayley Transform Darboux: dg hw
-- statement:
--   The Cayley Transform Darboux construction uses the dg hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L191-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L191-L194

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.dg_hw {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} (h : I → ℝ) {Λ : ι → I → ℂ} {f : M}
    (hf : ∀ w a, act (un w a a) f = Λ w a • f) : f ∈ (act (dg ι h)).eigenspace (∑ w, ∑ a, h a * Λ w a) := by sorry
