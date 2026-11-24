-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_measurable_ratPosDens_6e6772a3a708
-- name    : P2M_GroundTheory_Heights__Heights_RatChartChangeVar_measurable_ratPosDens_6e6772a3a708
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:40.118152+00:00
-- url     : https://prove2.me/theorems/4c9ef0a3-bd71-4fa4-96a3-eb38c789bd09
-- title:
--   P2 M Ground Theory Heights  Heights Rat Chart Change Var measurable rat Pos Dens 6e6772a3a708: P2 M Ground Theory Heights  Heights Rat Chart Change Var measurable rat Pos Dens 6e6772a3a708
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Chart Change Var measurable rat Pos Dens 6e6772a3a708 construction uses the P2 M Ground Theory Heights  Heights Rat Chart Change Var measurable rat Pos Dens 6e6772a3a708 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L39-L44

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

theorem P2M_GroundTheory_Heights__Heights_RatChartChangeVar_measurable_ratPosDens_6e6772a3a708 (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (RatChart.ratPosDens J p q f φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatChartChangeVar».«measurable_ratPosDens» := P2M_GroundTheory_Heights__Heights_RatChartChangeVar_measurable_ratPosDens_6e6772a3a708
