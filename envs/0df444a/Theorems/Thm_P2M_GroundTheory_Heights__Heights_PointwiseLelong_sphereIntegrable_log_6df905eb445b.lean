-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_log_6df905eb445b
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_log_6df905eb445b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:43.209901+00:00
-- url     : https://prove2.me/theorems/996546c0-5947-41d7-84a8-c6c18b0f46b0
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable log 6df905eb445b: P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable log 6df905eb445b
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable log 6df905eb445b construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable log 6df905eb445b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L135-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_log_6df905eb445b {Q : MvPolynomial (Fin N) ℂ} (hQ : Q ≠ 0) :
    SphereIntegrable (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«sphereIntegrable_log» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_log_6df905eb445b
