-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThKR_Mp_C_toBlocks___mul_lo_68e53e420ba7
-- name    : P2M_PositivityTheory_ThKR_Mp_C_toBlocks___mul_lo_68e53e420ba7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:43.621203+00:00
-- url     : https://prove2.me/theorems/4cca747d-0425-4560-9fbe-10d9384044e8
-- title:
--   P2 M Positivity Theory Th KR Mp C to Blocks   mul lo 68e53e420ba7: P2 M Positivity Theory Th KR Mp C to Blocks   mul lo 68e53e420ba7
-- statement:
--   The P2 M Positivity Theory Th KR Mp C to Blocks   mul lo 68e53e420ba7 construction uses the P2 M Positivity Theory Th KR Mp C to Blocks   mul lo 68e53e420ba7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean#L159-L161

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

theorem P2M_PositivityTheory_ThKR_Mp_C_toBlocks___mul_lo_68e53e420ba7 (s : Mat l) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by sorry

alias «PositivityTheory».«ThKR».«Mp».«C».«toBlocks₁₁_mul_lo» := P2M_PositivityTheory_ThKR_Mp_C_toBlocks___mul_lo_68e53e420ba7
