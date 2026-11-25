-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_FourInj_real_ae_zero
-- name    : PositivityTheory.ThKEst.FourInj.real_ae_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:04.820448+00:00
-- url     : https://prove2.me/theorems/86df2342-1421-41ae-9cfb-e0741b06f37a
-- title:
--   Four Inj: real ae zero
-- statement:
--   The Four Inj construction uses the real ae zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/FourierInjA.lean#L18-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/FourierInjA.lean#L18-L87

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_FourierInjA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory BoundedContinuousFunction
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.FourInj
variable {X A : Type} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

theorem PositivityTheory.ThKEst.FourInj.real_ae_zero (μ : Measure X) (e : A → X →ᵇ ℂ) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b)
    (hstar : ∀ a, ∃ c, e c = star (e a)) (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y) {h : X → ℝ}
    (hi : Integrable h μ) (h0 : ∀ a, ∫ x, h x • e a x ∂μ = 0) : h =ᵐ[μ] 0 := by sorry
