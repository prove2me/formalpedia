-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_of_pow_eq_one_41b87c66c74a
-- name    : P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_of_pow_eq_one_41b87c66c74a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:47.114408+00:00
-- url     : https://prove2.me/theorems/fa9ddb81-a710-4308-8ef3-4caa97deba85
-- title:
--   P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral of pow eq one 41b87c66c74a: P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral of pow eq one 41b87c66c74a
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral of pow eq one 41b87c66c74a construction uses the P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral of pow eq one 41b87c66c74a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L14-L16

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

theorem P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_of_pow_eq_one_41b87c66c74a {x : ℂ} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) : IsIntegral ℤ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootArithmeticVariety».«isIntegral_of_pow_eq_one» := P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_of_pow_eq_one_41b87c66c74a
