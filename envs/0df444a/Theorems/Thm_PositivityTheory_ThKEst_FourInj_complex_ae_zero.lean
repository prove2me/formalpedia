-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_FourInj_complex_ae_zero
-- name    : PositivityTheory.ThKEst.FourInj.complex_ae_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:47.633251+00:00
-- url     : https://prove2.me/theorems/b0b5991e-ad4e-4869-afb9-42f43db01a10
-- title:
--   Four Inj: complex ae zero
-- statement:
--   The Four Inj construction uses the complex ae zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/FourierInjA.lean#L89-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/FourierInjA.lean#L89-L118

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

theorem PositivityTheory.ThKEst.FourInj.complex_ae_zero (μ : Measure X) (e : A → X →ᵇ ℂ) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b)
    (hstar : ∀ a, ∃ c, e c = star (e a)) (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y) {H : X → ℂ}
    (hi : Integrable H μ) (h0 : ∀ a, ∫ x, e a x * H x ∂μ = 0) : H =ᵐ[μ] 0 := by sorry
