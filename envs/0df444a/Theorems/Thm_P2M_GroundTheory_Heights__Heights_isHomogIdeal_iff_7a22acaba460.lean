-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460
-- name    : P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:45.826548+00:00
-- url     : https://prove2.me/theorems/745e2bad-c9f6-4b79-8d4b-bc56b18dbf45
-- title:
--   P2 M Ground Theory Heights  Heights is Homog Ideal iff 7a22acaba460: P2 M Ground Theory Heights  Heights is Homog Ideal iff 7a22acaba460
-- statement:
--   The P2 M Ground Theory Heights  Heights is Homog Ideal iff 7a22acaba460 construction uses the P2 M Ground Theory Heights  Heights is Homog Ideal iff 7a22acaba460 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L84-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460 (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isHomogIdeal_iff» := P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460
