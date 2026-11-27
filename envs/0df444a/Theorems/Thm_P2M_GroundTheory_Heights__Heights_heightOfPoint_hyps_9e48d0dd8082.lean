-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_heightOfPoint_hyps_9e48d0dd8082
-- name    : P2M_GroundTheory_Heights__Heights_heightOfPoint_hyps_9e48d0dd8082
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:04.851322+00:00
-- url     : https://prove2.me/theorems/dc27b26c-da50-4f88-a85d-65a343920707
-- title:
--   P2 M Ground Theory Heights  Heights height Of Point hyps 9e48d0dd8082: P2 M Ground Theory Heights  Heights height Of Point hyps 9e48d0dd8082
-- statement:
--   The P2 M Ground Theory Heights  Heights height Of Point hyps 9e48d0dd8082 construction uses the P2 M Ground Theory Heights  Heights height Of Point hyps 9e48d0dd8082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L319-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L319-L329

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

theorem P2M_GroundTheory_Heights__Heights_heightOfPoint_hyps_9e48d0dd8082 :
    Submodule.span (𝓞 ℚ) (Set.range (Pi.basisFun (𝓞 ℚ) (Fin 2))) = ⊤ ∧ ratPointVec ≠ 0 ∧
      ratPointVec (Pi.basisFun (𝓞 ℚ) (Fin 2) 0) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«heightOfPoint_hyps» := P2M_GroundTheory_Heights__Heights_heightOfPoint_hyps_9e48d0dd8082
