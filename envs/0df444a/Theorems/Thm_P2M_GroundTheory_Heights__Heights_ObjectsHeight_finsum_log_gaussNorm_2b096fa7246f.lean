-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:44.410797+00:00
-- url     : https://prove2.me/theorems/e2226ab4-2ed1-40b7-9ce3-9dbee01c7024
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height finsum log gauss Norm 2b096fa7246f: P2 M Ground Theory Heights  Heights Objects Height finsum log gauss Norm 2b096fa7246f
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height finsum log gauss Norm 2b096fa7246f construction uses the P2 M Ground Theory Heights  Heights Objects Height finsum log gauss Norm 2b096fa7246f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L353-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L353-L365

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (f : MvPolynomial ι K) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
      ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
        Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm v.1 f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«finsum_log_gaussNorm» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f
