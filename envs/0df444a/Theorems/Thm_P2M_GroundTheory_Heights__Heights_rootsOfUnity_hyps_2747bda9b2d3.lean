-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rootsOfUnity_hyps_2747bda9b2d3
-- name    : P2M_GroundTheory_Heights__Heights_rootsOfUnity_hyps_2747bda9b2d3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:49.065127+00:00
-- url     : https://prove2.me/theorems/7116e025-05e1-4769-8100-14200647146f
-- title:
--   P2 M Ground Theory Heights  Heights roots Of Unity hyps 2747bda9b2d3: P2 M Ground Theory Heights  Heights roots Of Unity hyps 2747bda9b2d3
-- statement:
--   The P2 M Ground Theory Heights  Heights roots Of Unity hyps 2747bda9b2d3 construction uses the P2 M Ground Theory Heights  Heights roots Of Unity hyps 2747bda9b2d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L246-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L246-L256

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

theorem P2M_GroundTheory_Heights__Heights_rootsOfUnity_hyps_2747bda9b2d3 :
    Nat.Prime 2 ∧ IsPrimitiveRoot (-1 : 𝓞 ℚ) 2 ∧ (1 : 𝓞 ℚ) ^ 2 = 1 ∧ (-1 : 𝓞 ℚ) ^ 2 = 1 ∧
      (1 : 𝓞 ℚ) ≠ -1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rootsOfUnity_hyps» := P2M_GroundTheory_Heights__Heights_rootsOfUnity_hyps_2747bda9b2d3
