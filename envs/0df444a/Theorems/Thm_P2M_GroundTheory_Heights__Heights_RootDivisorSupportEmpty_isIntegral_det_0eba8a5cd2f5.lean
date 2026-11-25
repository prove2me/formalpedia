-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_det_0eba8a5cd2f5
-- name    : P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_det_0eba8a5cd2f5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:52.746336+00:00
-- url     : https://prove2.me/theorems/18b97f5a-ff02-56e2-8863-92744d10b2ac
-- title:
--   P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral det 0eba8a5cd2f5: P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral det 0eba8a5cd2f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral det 0eba8a5cd2f5 construction uses the P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral det 0eba8a5cd2f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDivSuppEmpty.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDivSuppEmpty.lean#L17-L24

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

theorem P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_det_0eba8a5cd2f5 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootDivisorSupportEmpty».«isIntegral_det» := P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_det_0eba8a5cd2f5
