-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_integrable_sphereLaw_eb6bacd4ac77
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_integrable_sphereLaw_eb6bacd4ac77
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:56.02172+00:00
-- url     : https://prove2.me/theorems/0d86214a-01a1-4dc1-be5f-d9a767337b9b
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong integrable sphere Law eb6bacd4ac77: P2 M Ground Theory Heights  Heights Pointwise Lelong integrable sphere Law eb6bacd4ac77
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong integrable sphere Law eb6bacd4ac77 construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong integrable sphere Law eb6bacd4ac77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L129-L133

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_integrable_sphereLaw_eb6bacd4ac77 {f : (Fin N → ℂ) → ℝ} (hf : Measurable f)
    (hi : SphereIntegrable (HermNorm.std N) 1 (fun u => f (fun j => u (0, j)))) :
    Integrable f (sphereLaw N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«integrable_sphereLaw» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_integrable_sphereLaw_eb6bacd4ac77
