-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_diagInv_mem_ff8cc4ad4488
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_diagInv_mem_ff8cc4ad4488
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:01.095209+00:00
-- url     : https://prove2.me/theorems/d4b4b307-4e3b-4ecf-a7d4-f9fd72419c6a
-- title:
--   P2 M Ground Theory Heights  Heights KCoord diag Inv mem ff8cc4ad4488: P2 M Ground Theory Heights  Heights KCoord diag Inv mem ff8cc4ad4488
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord diag Inv mem ff8cc4ad4488 construction uses the P2 M Ground Theory Heights  Heights KCoord diag Inv mem ff8cc4ad4488 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L58-L67

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_diagInv_mem_ff8cc4ad4488 (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    diagInv Y ∈ symplecticGroup (Fin g) ℝ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«diagInv_mem» := P2M_GroundTheory_Heights__Heights_KCoord_diagInv_mem_ff8cc4ad4488
