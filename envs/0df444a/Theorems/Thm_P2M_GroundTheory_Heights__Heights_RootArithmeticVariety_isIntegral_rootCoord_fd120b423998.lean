-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_rootCoord_fd120b423998
-- name    : P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_rootCoord_fd120b423998
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:51.916082+00:00
-- url     : https://prove2.me/theorems/3fe5a404-4f0e-4ba2-8764-0f7790f460e9
-- title:
--   P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral root Coord fd120b423998: P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral root Coord fd120b423998
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral root Coord fd120b423998 construction uses the P2 M Ground Theory Heights  Heights Root Arithmetic Variety is Integral root Coord fd120b423998 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootArithVar.lean#L36-L42

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

theorem P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_rootCoord_fd120b423998 {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootArithmeticVariety».«isIntegral_rootCoord» := P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_rootCoord_fd120b423998
