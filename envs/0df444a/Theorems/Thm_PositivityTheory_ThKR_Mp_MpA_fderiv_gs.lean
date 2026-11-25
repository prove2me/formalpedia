-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_MpA_fderiv_gs
-- name    : PositivityTheory.ThKR.Mp.MpA.fderiv_gs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:38.900959+00:00
-- url     : https://prove2.me/theorems/ac04343a-2177-5130-819d-54c13c3bcf80
-- title:
--   Mp A: fderiv gs
-- statement:
--   The Mp A construction uses the fderiv gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousTo.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousTo.lean#L61-L71

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpA

theorem PositivityTheory.ThKR.Mp.MpA.fderiv_gs (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(gs l)) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * gs l x = 0 := by sorry
