-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_unit_two_53614083cda1
-- name    : P2M_GroundTheory_Heights__Heights_unit_two_53614083cda1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:03.904403+00:00
-- url     : https://prove2.me/theorems/e12b45b5-daf9-4968-8b9e-f92f494ea17a
-- title:
--   P2 M Ground Theory Heights  Heights unit two 53614083cda1: P2 M Ground Theory Heights  Heights unit two 53614083cda1
-- statement:
--   The P2 M Ground Theory Heights  Heights unit two 53614083cda1 construction uses the P2 M Ground Theory Heights  Heights unit two 53614083cda1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L299-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L299-L300

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
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
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_unit_two_53614083cda1 : ∑ j, ‖(Pi.single 0 1 : Fin 2 → ℂ) j‖ ^ 2 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«unit_two» := P2M_GroundTheory_Heights__Heights_unit_two_53614083cda1
