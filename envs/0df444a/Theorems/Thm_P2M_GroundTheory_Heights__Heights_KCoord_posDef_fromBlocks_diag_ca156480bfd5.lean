-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_posDef_fromBlocks_diag_ca156480bfd5
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_posDef_fromBlocks_diag_ca156480bfd5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:24.549508+00:00
-- url     : https://prove2.me/theorems/d2735d16-a0e3-4ae8-911f-ac13afd69a6f
-- title:
--   P2 M Ground Theory Heights  Heights KCoord pos Def from Blocks diag ca156480bfd5: P2 M Ground Theory Heights  Heights KCoord pos Def from Blocks diag ca156480bfd5
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord pos Def from Blocks diag ca156480bfd5 construction uses the P2 M Ground Theory Heights  Heights KCoord pos Def from Blocks diag ca156480bfd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L13-L33

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
open GroundTheory.Heights₂.Heights.KCoord
variable {m n : Type*} [Fintype m] [Fintype n]

theorem P2M_GroundTheory_Heights__Heights_KCoord_posDef_fromBlocks_diag_ca156480bfd5 {A : Matrix m m ℝ} {D : Matrix n n ℝ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«posDef_fromBlocks_diag» := P2M_GroundTheory_Heights__Heights_KCoord_posDef_fromBlocks_diag_ca156480bfd5
