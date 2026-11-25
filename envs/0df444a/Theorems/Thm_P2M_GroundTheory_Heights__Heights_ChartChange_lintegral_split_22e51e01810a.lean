-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_lintegral_split_22e51e01810a
-- name    : P2M_GroundTheory_Heights__Heights_ChartChange_lintegral_split_22e51e01810a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:44.685661+00:00
-- url     : https://prove2.me/theorems/333e2f2d-b32d-4e22-9174-d76ce4879ec3
-- title:
--   P2 M Ground Theory Heights  Heights Chart Change lintegral split 22e51e01810a: P2 M Ground Theory Heights  Heights Chart Change lintegral split 22e51e01810a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Change lintegral split 22e51e01810a construction uses the P2 M Ground Theory Heights  Heights Chart Change lintegral split 22e51e01810a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L58-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChange_lintegral_split_22e51e01810a {K : Ideal (MvPolynomial (Fin n) ℂ)} {B : Matrix (Fin d) (Fin n) ℂ}
    {w : (Fin n → ℂ) → ℝ} (ψ : Fin d → (Fin n → ℂ) → ℝ) {F : ℕ → Set (Fin n → ℂ)}
    (hB : IsFiniteProjection K B) (hw : Measurable w) (hFm : ∀ k, MeasurableSet (F k))
    (h : ∀ᵐ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y)) :
    ∫⁻ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChange».«lintegral_split» := P2M_GroundTheory_Heights__Heights_ChartChange_lintegral_split_22e51e01810a
