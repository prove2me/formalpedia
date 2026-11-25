-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratDens_eq_posParts_46417a6351ab
-- name    : P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratDens_eq_posParts_46417a6351ab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:43.704985+00:00
-- url     : https://prove2.me/theorems/33f95890-5436-452b-8ced-eef5e22822ad
-- title:
--   P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Dens eq pos Parts 46417a6351ab: P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Dens eq pos Parts 46417a6351ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Dens eq pos Parts 46417a6351ab construction uses the P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Dens eq pos Parts 46417a6351ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L21-L31

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

theorem P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratDens_eq_posParts_46417a6351ab {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfin : (RatChart.ratFibre J p q y).Finite) :
    RatChart.ratAbsDens J p q f φ y = RatChart.ratPosDens J p q f φ y + RatChart.ratPosDens J p q (-f) φ y ∧
      RatChart.ratDens J p q f φ y = RatChart.ratPosDens J p q f φ y - RatChart.ratPosDens J p q (-f) φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatChartChangeVar».«ratDens_eq_posParts» := P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratDens_eq_posParts_46417a6351ab
