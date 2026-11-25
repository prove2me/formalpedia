-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_coord_e75478f7b92c
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_coord_e75478f7b92c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:44.960376+00:00
-- url     : https://prove2.me/theorems/b21b44b6-c0b6-49df-a61a-9c16be705646
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable coord e75478f7b92c: P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable coord e75478f7b92c
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable coord e75478f7b92c construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Integrable coord e75478f7b92c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L146-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L146-L161

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_coord_e75478f7b92c {p : Fin N → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    SphereIntegrable (HermNorm.std N) 1 (fun u ↦ Real.log ‖coordAlong p (fun j ↦ u (0, j))‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«sphereIntegrable_coord» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_coord_e75478f7b92c
