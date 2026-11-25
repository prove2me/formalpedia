-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_schwartzZippel_hyps_b595fc4537ee
-- name    : P2M_GroundTheory_Heights__Heights_schwartzZippel_hyps_b595fc4537ee
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:47:48.906339+00:00
-- url     : https://prove2.me/theorems/a346794d-81de-5bc6-a4fe-e371b7edf18e
-- title:
--   P2 M Ground Theory Heights  Heights schwartz Zippel hyps b595fc4537ee: P2 M Ground Theory Heights  Heights schwartz Zippel hyps b595fc4537ee
-- statement:
--   The P2 M Ground Theory Heights  Heights schwartz Zippel hyps b595fc4537ee construction uses the P2 M Ground Theory Heights  Heights schwartz Zippel hyps b595fc4537ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L235-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L235-L239

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

theorem P2M_GroundTheory_Heights__Heights_schwartzZippel_hyps_b595fc4537ee :
    (X 0 : MvPolynomial (Fin 2) ℤ) ≠ 0 ∧ ∀ i, (X 0 : MvPolynomial (Fin 2) ℤ).degreeOf i ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«schwartzZippel_hyps» := P2M_GroundTheory_Heights__Heights_schwartzZippel_hyps_b595fc4537ee
