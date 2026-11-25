-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_nonneg_662d6e890f87
-- name    : P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_nonneg_662d6e890f87
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:21:43.66362+00:00
-- url     : https://prove2.me/theorems/d01c7c43-b6f4-5ba4-bc35-89c0251a6217
-- title:
--   P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens nonneg 662d6e890f87: P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens nonneg 662d6e890f87
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens nonneg 662d6e890f87 construction uses the P2 M Ground Theory Heights  Heights Rat Chart Change Var rat Pos Dens nonneg 662d6e890f87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L33-L37

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

theorem P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_nonneg_662d6e890f87 (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ RatChart.ratPosDens J p q f φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatChartChangeVar».«ratPosDens_nonneg» := P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_nonneg_662d6e890f87
