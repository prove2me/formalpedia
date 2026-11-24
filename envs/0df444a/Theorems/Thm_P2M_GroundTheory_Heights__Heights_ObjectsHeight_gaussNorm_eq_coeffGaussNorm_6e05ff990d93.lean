-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_gaussNorm_eq_coeffGaussNorm_6e05ff990d93
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_gaussNorm_eq_coeffGaussNorm_6e05ff990d93
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:26.855384+00:00
-- url     : https://prove2.me/theorems/f55aca0e-eb86-4a59-8503-95f471928420
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height gauss Norm eq coeff Gauss Norm 6e05ff990d93: P2 M Ground Theory Heights  Heights Objects Height gauss Norm eq coeff Gauss Norm 6e05ff990d93
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height gauss Norm eq coeff Gauss Norm 6e05ff990d93 construction uses the P2 M Ground Theory Heights  Heights Objects Height gauss Norm eq coeff Gauss Norm 6e05ff990d93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L327-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L327-L351

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_gaussNorm_eq_coeffGaussNorm_6e05ff990d93 {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (f : MvPolynomial ι K) :
    gaussNorm v f = ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm (HeightOneSpectrum.adicAbv K v) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«gaussNorm_eq_coeffGaussNorm» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_gaussNorm_eq_coeffGaussNorm_6e05ff990d93
