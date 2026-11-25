-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaNormMajorant_isSymm_of_posDef_17a751f32486
-- name    : P2M_GroundTheory_Heights__Heights_KThetaNormMajorant_isSymm_of_posDef_17a751f32486
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:03.439663+00:00
-- url     : https://prove2.me/theorems/44a265dc-71cd-4579-ad70-826d18d7b317
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Norm Majorant is Symm of pos Def 17a751f32486: P2 M Ground Theory Heights  Heights KTheta Norm Majorant is Symm of pos Def 17a751f32486
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Norm Majorant is Symm of pos Def 17a751f32486 construction uses the P2 M Ground Theory Heights  Heights KTheta Norm Majorant is Symm of pos Def 17a751f32486 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaNormMajorant.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaNormMajorant.lean#L12-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaNormMajorant
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
open Matrix Real
open GroundTheory.Heights₂.Heights.KThetaNormMajorant

theorem P2M_GroundTheory_Heights__Heights_KThetaNormMajorant_isSymm_of_posDef_17a751f32486 {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) : Y.IsSymm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaNormMajorant».«isSymm_of_posDef» := P2M_GroundTheory_Heights__Heights_KThetaNormMajorant_isSymm_of_posDef_17a751f32486
