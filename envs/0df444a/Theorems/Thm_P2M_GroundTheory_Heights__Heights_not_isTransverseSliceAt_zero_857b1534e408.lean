-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_isTransverseSliceAt_zero_857b1534e408
-- name    : P2M_GroundTheory_Heights__Heights_not_isTransverseSliceAt_zero_857b1534e408
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:38.483363+00:00
-- url     : https://prove2.me/theorems/2d0e82b6-3d37-5b44-a538-5df8599addb5
-- title:
--   P2 M Ground Theory Heights  Heights not is Transverse Slice At zero 857b1534e408: P2 M Ground Theory Heights  Heights not is Transverse Slice At zero 857b1534e408
-- statement:
--   The P2 M Ground Theory Heights  Heights not is Transverse Slice At zero 857b1534e408 construction uses the P2 M Ground Theory Heights  Heights not is Transverse Slice At zero 857b1534e408 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L78-L90

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

theorem P2M_GroundTheory_Heights__Heights_not_isTransverseSliceAt_zero_857b1534e408 :
    ¬ IsTransverseSliceAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«not_isTransverseSliceAt_zero» := P2M_GroundTheory_Heights__Heights_not_isTransverseSliceAt_zero_857b1534e408
