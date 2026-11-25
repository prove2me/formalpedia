-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_rootCoord_isIntegral_4297a36abd8e
-- name    : P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_rootCoord_isIntegral_4297a36abd8e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:11.38612+00:00
-- url     : https://prove2.me/theorems/94956cb4-2f51-4f63-9d92-cb6c0b2934e0
-- title:
--   P2 M Ground Theory Heights  Heights Root Points Finite Alt root Coord is Integral 4297a36abd8e: P2 M Ground Theory Heights  Heights Root Points Finite Alt root Coord is Integral 4297a36abd8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Points Finite Alt root Coord is Integral 4297a36abd8e construction uses the P2 M Ground Theory Heights  Heights Root Points Finite Alt root Coord is Integral 4297a36abd8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L50-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointsFinite
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
open GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
variable {K : Type*} {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_rootCoord_isIntegral_4297a36abd8e {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointsFiniteAlt».«rootCoord_isIntegral» := P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_rootCoord_isIntegral_4297a36abd8e
