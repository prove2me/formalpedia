-- Prove2me | Theorems.Thm_P2M_CompanionTheory_ThKR_Mp_C_toBlocks___mul_lo_fbd01804b3f9
-- name    : P2M_CompanionTheory_ThKR_Mp_C_toBlocks___mul_lo_fbd01804b3f9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:36.686237+00:00
-- url     : https://prove2.me/theorems/4afa4fd8-4c5a-4757-9ab5-84337297ac6e
-- title:
--   P2 M Companion Theory Th KR Mp C to Blocks   mul lo fbd01804b3f9: P2 M Companion Theory Th KR Mp C to Blocks   mul lo fbd01804b3f9
-- statement:
--   The P2 M Companion Theory Th KR Mp C to Blocks   mul lo fbd01804b3f9 construction uses the P2 M Companion Theory Th KR Mp C to Blocks   mul lo fbd01804b3f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L159-L161

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C
open CompanionTheory.ThKR.Mp.C

theorem P2M_CompanionTheory_ThKR_Mp_C_toBlocks___mul_lo_fbd01804b3f9 (s : Mat l) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by sorry

alias «CompanionTheory».«ThKR».«Mp».«C».«toBlocks₁₁_mul_lo» := P2M_CompanionTheory_ThKR_Mp_C_toBlocks___mul_lo_fbd01804b3f9
