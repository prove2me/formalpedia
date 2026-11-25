-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_existsUnique_siegelGram_9ab454a621dd
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_existsUnique_siegelGram_9ab454a621dd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:02.222122+00:00
-- url     : https://prove2.me/theorems/583a768e-c178-4d79-bfeb-398397e1652f
-- title:
--   P2 M Ground Theory Heights  Heights KCoord exists Unique siegel Gram 9ab454a621dd: P2 M Ground Theory Heights  Heights KCoord exists Unique siegel Gram 9ab454a621dd
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord exists Unique siegel Gram 9ab454a621dd construction uses the P2 M Ground Theory Heights  Heights KCoord exists Unique siegel Gram 9ab454a621dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L88-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L88-L157

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_existsUnique_siegelGram_9ab454a621dd (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (hS : G ∈ symplecticGroup (Fin g) ℝ) (hG : G.PosDef) :
    ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
      XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«existsUnique_siegelGram» := P2M_GroundTheory_Heights__Heights_KCoord_existsUnique_siegelGram_9ab454a621dd
