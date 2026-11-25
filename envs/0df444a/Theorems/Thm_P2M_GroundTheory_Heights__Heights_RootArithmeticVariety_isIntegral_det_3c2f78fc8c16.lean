-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_det_3c2f78fc8c16
-- name    : P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_det_3c2f78fc8c16
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:43.054209+00:00
-- url     : https://prove2.me/theorems/dae2b9e4-283c-5a41-87c4-aee6c1aaf270
-- title:
--   P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral det 3c2f78fc8c16: P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral det 3c2f78fc8c16
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral det 3c2f78fc8c16 construction uses the P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral det 3c2f78fc8c16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L18-L23

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

theorem P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_det_3c2f78fc8c16 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootArithmeticVariety».«isIntegral_det» := P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_det_3c2f78fc8c16
