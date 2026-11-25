-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_onePipe_mul_conjTranspose_f82578e1cf02
-- name    : P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_onePipe_mul_conjTranspose_f82578e1cf02
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:35.42072+00:00
-- url     : https://prove2.me/theorems/fd87ad58-443c-49ba-90d7-2abb328970e4
-- title:
--   P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt one Pipe mul conj Transpose f82578e1cf02: P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt one Pipe mul conj Transpose f82578e1cf02
-- statement:
--   The P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt one Pipe mul conj Transpose f82578e1cf02 construction uses the P2 M Ground Theory Heights  Heights Pluecker Norm Sq Alt one Pipe mul conj Transpose f82578e1cf02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerNormSq.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerNormSq.lean#L13-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerNormSq
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
open Matrix Finset
noncomputable section
open GroundTheory.Heights₂.Heights.PlueckerNormSqAlt

theorem P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_onePipe_mul_conjTranspose_f82578e1cf02 {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    onePipe Z * (onePipe Z)ᴴ = 1 + Z * Zᴴ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlueckerNormSqAlt».«onePipe_mul_conjTranspose» := P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_onePipe_mul_conjTranspose_f82578e1cf02
