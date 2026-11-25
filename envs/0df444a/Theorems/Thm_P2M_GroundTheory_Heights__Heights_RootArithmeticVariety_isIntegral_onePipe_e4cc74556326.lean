-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_onePipe_e4cc74556326
-- name    : P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_onePipe_e4cc74556326
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:41.841876+00:00
-- url     : https://prove2.me/theorems/e30d8716-8246-53cb-99a2-cb062bfbb55c
-- title:
--   P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral one Pipe e4cc74556326: P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral one Pipe e4cc74556326
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral one Pipe e4cc74556326 construction uses the P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral one Pipe e4cc74556326 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L25-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootArithVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootArithmeticVariety

theorem P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_onePipe_e4cc74556326 {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, IsIntegral ℤ (Z a b))
    (a : Fin j) (b : Fin (j + m)) : IsIntegral ℤ (onePipe Z a b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootArithmeticVariety».«isIntegral_onePipe» := P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_onePipe_e4cc74556326
