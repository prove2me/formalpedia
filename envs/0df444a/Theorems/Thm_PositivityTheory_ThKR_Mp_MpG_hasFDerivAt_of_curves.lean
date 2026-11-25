-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_MpG_hasFDerivAt_of_curves
-- name    : PositivityTheory.ThKR.Mp.MpG.hasFDerivAt_of_curves
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:05.343181+00:00
-- url     : https://prove2.me/theorems/c015f301-cf65-412a-b76d-8ac6e0092702
-- title:
--   Mp G: has FDeriv At of curves
-- statement:
--   The Mp G construction uses the has FDeriv At of curves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOfCurves.lean#L10-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOfCurves.lean#L10-L57

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_HasFDerivAtOfCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp PositivityTheory.ThKR.Mp.MpG

theorem PositivityTheory.ThKR.Mp.MpG.hasFDerivAt_of_curves {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : E → F} {L : E →L[ℝ] F} {x₀ : E}
    (h : ∀ (c : ℝ → E) (v : E), c 0 = x₀ → HasDerivAt c v 0 → HasDerivAt (fun t => Φ (c t)) (L v) 0) :
    HasFDerivAt Φ L x₀ := by sorry
