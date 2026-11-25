-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_finMean_add_3fcf64c86f89
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_finMean_add_3fcf64c86f89
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:07.326273+00:00
-- url     : https://prove2.me/theorems/34cd4205-3f6c-4321-a655-2c4cae09e750
-- title:
--   P2 M Ground Theory Heights  Heights KCoord fin Mean add 3fcf64c86f89: P2 M Ground Theory Heights  Heights KCoord fin Mean add 3fcf64c86f89
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord fin Mean add 3fcf64c86f89 construction uses the P2 M Ground Theory Heights  Heights KCoord fin Mean add 3fcf64c86f89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L21-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordWeak
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
open Real
open GroundTheory.Heights₂.Heights.KCoord
variable {S : Type*} [Fintype S]

theorem P2M_GroundTheory_Heights__Heights_KCoord_finMean_add_3fcf64c86f89 (f h : S → ℝ) : finMean (fun s => f s + h s) = finMean f + finMean h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«finMean_add» := P2M_GroundTheory_Heights__Heights_KCoord_finMean_add_3fcf64c86f89
