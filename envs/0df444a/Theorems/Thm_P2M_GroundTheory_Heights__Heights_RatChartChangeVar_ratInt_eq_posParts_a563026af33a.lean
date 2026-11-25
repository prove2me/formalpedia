-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratInt_eq_posParts_a563026af33a
-- name    : P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratInt_eq_posParts_a563026af33a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:39.51107+00:00
-- url     : https://prove2.me/theorems/caf3838f-3b28-4ca1-8f8d-74900740b712
-- title:
--   P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Int eq pos Parts a563026af33a: P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Int eq pos Parts a563026af33a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Int eq pos Parts a563026af33a construction uses the P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Int eq pos Parts a563026af33a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L46-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L46-L85

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

theorem P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratInt_eq_posParts_a563026af33a (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (RatChart.ratAbsDens J p q f φ) ↔
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)) +
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y) < ⊤) ∧
    (Integrable (RatChart.ratAbsDens J p q f φ) → ∫ y, RatChart.ratDens J p q f φ y =
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y)).toReal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatChartChangeVar».«ratInt_eq_posParts» := P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratInt_eq_posParts_a563026af33a
