-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_C_lo_mem
-- name    : PositivityTheory.ThKR.Mp.C.lo_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:31.680054+00:00
-- url     : https://prove2.me/theorems/2bb08760-0044-592c-b9a9-cb65ce0290b8
-- title:
--   C: lo mem
-- statement:
--   The C construction uses the lo mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L151-L153

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
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
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C
open PositivityTheory.ThKR.Mp.C

theorem PositivityTheory.ThKR.Mp.C.lo_mem (t : ℝ) : lo (l := l) t ∈ Matrix.symplecticGroup l ℝ := by sorry
