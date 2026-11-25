-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_e164410b85a6
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_e164410b85a6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:39.30997+00:00
-- url     : https://prove2.me/theorems/d2396cc2-4a8b-4895-9076-53d7e4d95f32
-- title:
--   P2 M Ground Theory Heights  Heights KCoord fin Mean const e164410b85a6: P2 M Ground Theory Heights  Heights KCoord fin Mean const e164410b85a6
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord fin Mean const e164410b85a6 construction uses the P2 M Ground Theory Heights  Heights KCoord fin Mean const e164410b85a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L30-L33

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_e164410b85a6 [Nonempty S] (c : ℝ) : finMean (fun _ : S => c) = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«finMean_const» := P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_e164410b85a6
