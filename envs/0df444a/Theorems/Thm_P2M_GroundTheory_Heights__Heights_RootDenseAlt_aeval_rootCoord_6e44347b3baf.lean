-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_rootCoord_6e44347b3baf
-- name    : P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_rootCoord_6e44347b3baf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:41.546292+00:00
-- url     : https://prove2.me/theorems/5c41264c-1444-401a-a297-7398eea91db9
-- title:
--   P2 M Ground Theory Heights  Heights Root Dense Alt aeval root Coord 6e44347b3baf: P2 M Ground Theory Heights  Heights Root Dense Alt aeval root Coord 6e44347b3baf
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Dense Alt aeval root Coord 6e44347b3baf construction uses the P2 M Ground Theory Heights  Heights Root Dense Alt aeval root Coord 6e44347b3baf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDense.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDense.lean#L27-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDense
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
open GroundTheory.Heights₂.Heights.RootDenseAlt

theorem P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_rootCoord_6e44347b3baf {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ) (g : MRing (plBlocks f j m)) :
    aeval (rootCoord (fun τ a b => x (τ, a, b))) g = aeval x (aeval (grassPolyCoord f j m) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootDenseAlt».«aeval_rootCoord» := P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_rootCoord_6e44347b3baf
