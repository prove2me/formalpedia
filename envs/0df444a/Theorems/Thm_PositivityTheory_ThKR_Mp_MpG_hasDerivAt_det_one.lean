-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_MpG_hasDerivAt_det_one
-- name    : PositivityTheory.ThKR.Mp.MpG.hasDerivAt_det_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:12.673873+00:00
-- url     : https://prove2.me/theorems/9dcbdbb8-25a4-5b7b-ad5b-5d9acb89a449
-- title:
--   Mp G: has Deriv At det one
-- statement:
--   The Mp G construction uses the has Deriv At det one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOfCurves.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOfCurves.lean#L61-L79

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
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.Mp.MpG.hasDerivAt_det_one {M : ℝ → l → l → ℝ} {X : l → l → ℝ} (h : HasDerivAt M X 0) (h0 : Matrix.of (M 0) = 1) :
    HasDerivAt (fun t => (Matrix.of (M t)).det) (Matrix.of X).trace 0 := by sorry
