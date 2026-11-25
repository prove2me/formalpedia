-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_posPart_eq_457a933ba476
-- name    : P2M_GroundTheory_Heights__Heights_RatChartChangeVar_posPart_eq_457a933ba476
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:21:20.639046+00:00
-- url     : https://prove2.me/theorems/01262171-a05f-5e01-b789-4d487848d212
-- title:
--   P2 M Ground Theory Heights  Heights Rat Chart Change Var pos Part eq 457a933ba476: P2 M Ground Theory Heights  Heights Rat Chart Change Var pos Part eq 457a933ba476
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Chart Change Var pos Part eq 457a933ba476 construction uses the P2 M Ground Theory Heights  Heights Rat Chart Change Var pos Part eq 457a933ba476 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L118-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L118-L180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
open GroundTheory.Heights₂.Heights.RatChartChangeVar
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatChartChangeVar_posPart_eq_457a933ba476 (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement)
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hq : q ∉ J) (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) (hf : Measurable f)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) :
    ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatChartChangeVar».«posPart_eq» := P2M_GroundTheory_Heights__Heights_RatChartChangeVar_posPart_eq_457a933ba476
