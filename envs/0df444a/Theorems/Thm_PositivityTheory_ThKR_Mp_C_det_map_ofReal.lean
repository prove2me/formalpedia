-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_C_det_map_ofReal
-- name    : PositivityTheory.ThKR.Mp.C.det_map_ofReal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:30.013688+00:00
-- url     : https://prove2.me/theorems/94ec0b6c-fb22-5971-ae02-bbca2f2c2ad1
-- title:
--   C: det map of Real
-- statement:
--   The C construction uses the det map of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L28-L29

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
open PositivityTheory.ThKR.Mp.C

theorem PositivityTheory.ThKR.Mp.C.det_map_ofReal (M : Matrix l l ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) := by sorry
