-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_heightOfCycle_hyp_4e3d46928265
-- name    : P2M_GroundTheory_Heights__Heights_heightOfCycle_hyp_4e3d46928265
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:30.849292+00:00
-- url     : https://prove2.me/theorems/ded1712b-61ea-5839-bfc1-76fac8382ffd
-- title:
--   P2 M Ground Theory Heights  Heights height Of Cycle hyp 4e3d46928265: P2 M Ground Theory Heights  Heights height Of Cycle hyp 4e3d46928265
-- statement:
--   The P2 M Ground Theory Heights  Heights height Of Cycle hyp 4e3d46928265 construction uses the P2 M Ground Theory Heights  Heights height Of Cycle hyp 4e3d46928265 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L331-L334

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

theorem P2M_GroundTheory_Heights__Heights_heightOfCycle_hyp_4e3d46928265 :
    (X 0 + C 2 * X 1 : MvPolynomial (Fin 2) ℚ).map (algebraMap ℚ ℚ) =
      C 1 * ∏ _q : Fin 1, ∑ k, C (ratPointVec (Pi.basisFun (𝓞 ℚ) (Fin 2) k)) * X k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«heightOfCycle_hyp» := P2M_GroundTheory_Heights__Heights_heightOfCycle_hyp_4e3d46928265
