-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_mem_posDef_2f7eb0d9c3c8
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_mem_posDef_2f7eb0d9c3c8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:55.551215+00:00
-- url     : https://prove2.me/theorems/5efbb58e-84b1-4142-a2ac-473357539e45
-- title:
--   P2 M Ground Theory Heights  Heights KCoord siegel Gram mem pos Def 2f7eb0d9c3c8: P2 M Ground Theory Heights  Heights KCoord siegel Gram mem pos Def 2f7eb0d9c3c8
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord siegel Gram mem pos Def 2f7eb0d9c3c8 construction uses the P2 M Ground Theory Heights  Heights KCoord siegel Gram mem pos Def 2f7eb0d9c3c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L73-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordSiegel
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
open Matrix
variable {g : ℕ}
open GroundTheory.Heights₂.Heights.KCoord

theorem P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_mem_posDef_2f7eb0d9c3c8 (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«siegelGram_mem_posDef» := P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_mem_posDef_2f7eb0d9c3c8
