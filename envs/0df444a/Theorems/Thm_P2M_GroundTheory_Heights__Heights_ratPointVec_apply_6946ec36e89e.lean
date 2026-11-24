-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratPointVec_apply_6946ec36e89e
-- name    : P2M_GroundTheory_Heights__Heights_ratPointVec_apply_6946ec36e89e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:03.5136+00:00
-- url     : https://prove2.me/theorems/d2038060-c21e-4359-bb51-98b59ec85ade
-- title:
--   P2 M Ground Theory Heights  Heights rat Point Vec apply 6946ec36e89e: P2 M Ground Theory Heights  Heights rat Point Vec apply 6946ec36e89e
-- statement:
--   The P2 M Ground Theory Heights  Heights rat Point Vec apply 6946ec36e89e construction uses the P2 M Ground Theory Heights  Heights rat Point Vec apply 6946ec36e89e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L317-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L317-L317

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

theorem P2M_GroundTheory_Heights__Heights_ratPointVec_apply_6946ec36e89e (x : Fin 2 → 𝓞 ℚ) : ratPointVec x = (x 0 : ℚ) + 2 * (x 1 : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratPointVec_apply» := P2M_GroundTheory_Heights__Heights_ratPointVec_apply_6946ec36e89e
