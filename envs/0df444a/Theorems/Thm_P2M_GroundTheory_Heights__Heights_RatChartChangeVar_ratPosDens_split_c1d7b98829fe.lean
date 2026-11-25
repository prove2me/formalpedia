-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_split_c1d7b98829fe
-- name    : P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_split_c1d7b98829fe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:52.694829+00:00
-- url     : https://prove2.me/theorems/6abb44cf-b422-4c4b-a904-51a91d5efcc1
-- title:
--   P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens split c1d7b98829fe: P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens split c1d7b98829fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens split c1d7b98829fe construction uses the P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens split c1d7b98829fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L87-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L87-L116

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

theorem P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_split_c1d7b98829fe {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (E : ℕ → Set (Fin n → ℂ)) (y : Fin d → ℂ) (hfin : (RatChart.ratFibre J p q y).Finite)
    (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ x ∈ RatChart.ratFibre J p q y, (∃ s, RatChart.IsRatSheetAt J p q x s) → ∃ k, x ∈ E k) :
    ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∑' k, ENNReal.ofReal (RatChart.ratPosDens J p q ((E k).indicator f) φ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatChartChangeVar».«ratPosDens_split» := P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_split_c1d7b98829fe
