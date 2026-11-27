-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rootCoord_mem_79dd987525e5
-- name    : P2M_GroundTheory_Heights__Heights_rootCoord_mem_79dd987525e5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:28.886025+00:00
-- url     : https://prove2.me/theorems/0c601809-deb9-576f-94ad-2caf44c3c16a
-- title:
--   P2 M Ground Theory Heights  Heights root Coord mem 79dd987525e5: P2 M Ground Theory Heights  Heights root Coord mem 79dd987525e5
-- statement:
--   The P2 M Ground Theory Heights  Heights root Coord mem 79dd987525e5 construction uses the P2 M Ground Theory Heights  Heights root Coord mem 79dd987525e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrassHeightNE.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrassHeightNE.lean#L35-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
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

theorem P2M_GroundTheory_Heights__Heights_rootCoord_mem_79dd987525e5 {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    rootCoord ζ ∈ mcPts (rootPointIdeal ζ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rootCoord_mem» := P2M_GroundTheory_Heights__Heights_rootCoord_mem_79dd987525e5
