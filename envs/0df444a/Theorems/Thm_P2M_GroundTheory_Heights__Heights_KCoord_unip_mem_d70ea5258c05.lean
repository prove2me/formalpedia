-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_unip_mem_d70ea5258c05
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_unip_mem_d70ea5258c05
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:04.883107+00:00
-- url     : https://prove2.me/theorems/89f8bad0-8e09-49ad-9434-318a52349044
-- title:
--   P2 M Ground Theory Heights  Heights KCoord unip mem d70ea5258c05: P2 M Ground Theory Heights  Heights KCoord unip mem d70ea5258c05
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord unip mem d70ea5258c05 construction uses the P2 M Ground Theory Heights  Heights KCoord unip mem d70ea5258c05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean#L52-L56

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_unip_mem_d70ea5258c05 (X : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    unip X ∈ symplecticGroup (Fin g) ℝ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«unip_mem» := P2M_GroundTheory_Heights__Heights_KCoord_unip_mem_d70ea5258c05
