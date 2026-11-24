-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_smul_d6bde57d50a9
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_smul_d6bde57d50a9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:59.076197+00:00
-- url     : https://prove2.me/theorems/667232e8-c171-41ad-994d-82934488f67b
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong eval smul d6bde57d50a9: P2 M Ground Theory Heights  Heights Pointwise Lelong eval smul d6bde57d50a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong eval smul d6bde57d50a9 construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong eval smul d6bde57d50a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L18-L25

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_smul_d6bde57d50a9 {Q : MvPolynomial (Fin N) ℂ} {d : ℕ} (hQ : Q.IsHomogeneous d) (t : ℂ)
    (x : Fin N → ℂ) : eval (t • x) Q = t ^ d * eval x Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«eval_smul» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_smul_d6bde57d50a9
