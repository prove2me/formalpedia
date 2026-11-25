-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_ld_dil_one
-- name    : PositivityTheory.ThKR.LL.ld_dil_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:57.59527+00:00
-- url     : https://prove2.me/theorems/eaceab8b-2de5-4922-bc55-a2b0f210f4de
-- title:
--   LL: ld dil one
-- statement:
--   The LL construction uses the ld dil one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L70-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L70-L108

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem PositivityTheory.ThKR.LL.ld_dil_one {H : ℝ → Eu l →L[ℝ] Eu l} {H' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt H H' t₀) (h0 : H t₀ = 1)
    (f : Sch l) {F : ℝ → Sch l} (hF : ∀ᶠ t in 𝓝 t₀, ∀ x, F t x = f (H t x)) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l (vf H' f)) t₀ := by sorry
