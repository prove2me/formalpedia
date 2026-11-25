-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_mul_25558bd2c98b
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_mul_25558bd2c98b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:10.201732+00:00
-- url     : https://prove2.me/theorems/07df45f8-e672-42fa-a632-a99e86f59984
-- title:
--   P2 M Ground Theory Heights  Heights KCoord fin Mean const mul 25558bd2c98b: P2 M Ground Theory Heights  Heights KCoord fin Mean const mul 25558bd2c98b
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord fin Mean const mul 25558bd2c98b construction uses the P2 M Ground Theory Heights  Heights KCoord fin Mean const mul 25558bd2c98b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L27-L28

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_mul_25558bd2c98b (c : ℝ) (f : S → ℝ) : finMean (fun s => c * f s) = c * finMean f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«finMean_const_mul» := P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_mul_25558bd2c98b
