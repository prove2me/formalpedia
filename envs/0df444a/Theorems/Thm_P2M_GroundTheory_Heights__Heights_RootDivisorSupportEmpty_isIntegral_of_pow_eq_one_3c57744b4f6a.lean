-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_of_pow_eq_one_3c57744b4f6a
-- name    : P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_of_pow_eq_one_3c57744b4f6a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:54.921414+00:00
-- url     : https://prove2.me/theorems/de2a28d0-66c9-4229-bdb0-16e371271b08
-- title:
--   P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral of pow eq one 3c57744b4f6a: P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral of pow eq one 3c57744b
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral of pow eq one 3c57744b4f6a construction uses the P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral of pow eq one 3c57744b4f6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDivSuppEmpty.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDivSuppEmpty.lean#L14-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDivSuppEmpty
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
open GroundTheory.Heights₂.Heights.RootDivisorSupportEmpty

theorem P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_of_pow_eq_one_3c57744b4f6a {z : ℂ} {k : ℕ} (hk : 0 < k) (hz : z ^ k = 1) : IsIntegral ℤ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootDivisorSupportEmpty».«isIntegral_of_pow_eq_one» := P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_of_pow_eq_one_3c57744b4f6a
