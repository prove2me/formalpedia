-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_finMean_sub_2af85f626cdf
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_finMean_sub_2af85f626cdf
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:08.805689+00:00
-- url     : https://prove2.me/theorems/90c7526b-eeb5-5cbe-bd77-de825f020195
-- title:
--   P2 M Ground Theory Heights  Heights KCoord fin Mean sub 2af85f626cdf: P2 M Ground Theory Heights  Heights KCoord fin Mean sub 2af85f626cdf
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord fin Mean sub 2af85f626cdf construction uses the P2 M Ground Theory Heights  Heights KCoord fin Mean sub 2af85f626cdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L24-L25

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_finMean_sub_2af85f626cdf (f h : S → ℝ) : finMean (fun s => f s - h s) = finMean f - finMean h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«finMean_sub» := P2M_GroundTheory_Heights__Heights_KCoord_finMean_sub_2af85f626cdf
