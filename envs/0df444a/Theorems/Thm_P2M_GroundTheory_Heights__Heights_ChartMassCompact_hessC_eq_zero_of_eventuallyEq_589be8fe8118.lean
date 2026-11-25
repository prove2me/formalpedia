-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_hessC_eq_zero_of_eventuallyEq_589be8fe8118
-- name    : P2M_GroundTheory_Heights__Heights_ChartMassCompact_hessC_eq_zero_of_eventuallyEq_589be8fe8118
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:11.564997+00:00
-- url     : https://prove2.me/theorems/15474dc4-27e7-41eb-b798-6b7c7a772538
-- title:
--   P2 M Ground Theory Heights  Heights Chart Mass Compact hess C eq zero of eventually Eq 589be8fe8118: P2 M Ground Theory Heights  Heights Chart Mass Compact hess C eq zero of eventually Eq 589be8fe8118
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Mass Compact hess C eq zero of eventually Eq 589be8fe8118 construction uses the P2 M Ground Theory Heights  Heights Chart Mass Compact hess C eq zero of eventually Eq 589be8fe8118 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L31-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMassCompact_hessC_eq_zero_of_eventuallyEq_589be8fe8118 {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] 0) : ReciprocityTheory.AnForm.hessC φ z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMassCompact».«hessC_eq_zero_of_eventuallyEq» := P2M_GroundTheory_Heights__Heights_ChartMassCompact_hessC_eq_zero_of_eventuallyEq_589be8fe8118
