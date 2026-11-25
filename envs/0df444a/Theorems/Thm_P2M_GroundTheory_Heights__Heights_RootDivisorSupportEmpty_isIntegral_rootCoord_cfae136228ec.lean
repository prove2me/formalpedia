-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_rootCoord_cfae136228ec
-- name    : P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_rootCoord_cfae136228ec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:33.297972+00:00
-- url     : https://prove2.me/theorems/a3fc8247-3cce-4918-a84d-ebfb782d1f1e
-- title:
--   P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral root Coord cfae136228ec: P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral root Coord cfae136228ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral root Coord cfae136228ec construction uses the P2 M Ground Theory Heights  Heights Root Divisor Support Empty is Integral root Coord cfae136228ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDivSuppEmpty.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDivSuppEmpty.lean#L26-L37

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

theorem P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_rootCoord_cfae136228ec {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootDivisorSupportEmpty».«isIntegral_rootCoord» := P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_rootCoord_cfae136228ec
