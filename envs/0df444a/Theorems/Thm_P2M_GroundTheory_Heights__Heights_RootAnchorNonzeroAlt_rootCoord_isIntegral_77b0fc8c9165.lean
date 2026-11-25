-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_rootCoord_isIntegral_77b0fc8c9165
-- name    : P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_rootCoord_isIntegral_77b0fc8c9165
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:04.192499+00:00
-- url     : https://prove2.me/theorems/01451549-d5e2-42c2-b4c3-2c27f9f101f7
-- title:
--   P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt root Coord is Integral 77b0fc8c9165: P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt root Coord is Integral 77b0fc8c9165
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt root Coord is Integral 77b0fc8c9165 construction uses the P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt root Coord is Integral 77b0fc8c9165 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L29-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
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
open GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt

theorem P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_rootCoord_isIntegral_77b0fc8c9165 {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootAnchorNonzeroAlt».«rootCoord_isIntegral» := P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_rootCoord_isIntegral_77b0fc8c9165
