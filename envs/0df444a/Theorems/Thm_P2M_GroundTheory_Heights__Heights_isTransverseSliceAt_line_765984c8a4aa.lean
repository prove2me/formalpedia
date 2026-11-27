-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isTransverseSliceAt_line_765984c8a4aa
-- name    : P2M_GroundTheory_Heights__Heights_isTransverseSliceAt_line_765984c8a4aa
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:32.747703+00:00
-- url     : https://prove2.me/theorems/6b4e617c-df36-50d6-b239-fa8719ea452a
-- title:
--   P2 M Ground Theory Heights  Heights is Transverse Slice At line 765984c8a4aa: P2 M Ground Theory Heights  Heights is Transverse Slice At line 765984c8a4aa
-- statement:
--   The P2 M Ground Theory Heights  Heights is Transverse Slice At line 765984c8a4aa construction uses the P2 M Ground Theory Heights  Heights is Transverse Slice At line 765984c8a4aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L55-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L55-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isTransverseSliceAt_line_765984c8a4aa :
    IsTransverseSliceAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isTransverseSliceAt_line» := P2M_GroundTheory_Heights__Heights_isTransverseSliceAt_line_765984c8a4aa
