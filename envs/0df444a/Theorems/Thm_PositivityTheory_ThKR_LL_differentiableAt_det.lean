-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_differentiableAt_det
-- name    : PositivityTheory.ThKR.LL.differentiableAt_det
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:06:24.261463+00:00
-- url     : https://prove2.me/theorems/6c6e1f56-7adc-4f01-9035-3171e7bf818b
-- title:
--   LL: differentiable At det
-- statement:
--   The LL construction uses the differentiable At det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L142-L145

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.LL.differentiableAt_det {M : ℝ → Matrix l l ℝ} {t : ℝ} (h : ∀ i j, DifferentiableAt ℝ (fun t => M t i j) t) :
    DifferentiableAt ℝ (fun t => (M t).det) t := by sorry
