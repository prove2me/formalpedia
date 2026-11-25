-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_C_map_ofReal_mul
-- name    : PositivityTheory.ThKR.Mp.C.map_ofReal_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:28.13959+00:00
-- url     : https://prove2.me/theorems/9db54ba3-a1c9-4ed2-a6d9-46ecdc39078e
-- title:
--   C: map of Real mul
-- statement:
--   The C construction uses the map of Real mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L23-L26

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

theorem PositivityTheory.ThKR.Mp.C.map_ofReal_mul (M N : Matrix l l ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by sorry
