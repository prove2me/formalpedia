-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_eq_e89b1c54405c
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_eq_e89b1c54405c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:11.02337+00:00
-- url     : https://prove2.me/theorems/b0fc04b2-38b3-4909-84b8-7514d3220ca4
-- title:
--   P2 M Ground Theory Heights  Heights KCoord siegel Gram eq e89b1c54405c: P2 M Ground Theory Heights  Heights KCoord siegel Gram eq e89b1c54405c
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord siegel Gram eq e89b1c54405c construction uses the P2 M Ground Theory Heights  Heights KCoord siegel Gram eq e89b1c54405c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L47-L50

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_eq_e89b1c54405c (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    siegelGram X Y = (unip X)ᵀ * diagInv Y * unip X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«siegelGram_eq» := P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_eq_e89b1c54405c
