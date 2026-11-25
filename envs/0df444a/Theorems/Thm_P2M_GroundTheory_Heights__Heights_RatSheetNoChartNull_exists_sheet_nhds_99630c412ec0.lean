-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_nhds_99630c412ec0
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_nhds_99630c412ec0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:08.576459+00:00
-- url     : https://prove2.me/theorems/4eb487b8-d6f2-4136-ba56-ff56ee5eaab6
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet nhds 99630c412ec0: P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet nhds 99630c412ec0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet nhds 99630c412ec0 construction uses the P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet nhds 99630c412ec0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L30-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_nhds_e46767207946

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
noncomputable section
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_nhds_99630c412ec0 {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, RatChart.ratMap p q x' ∈ U ∧ RatChart.IsRatSheetAt J p q x' s) ∧
      ((∃ s, RatChart.IsRatSheetAt J p q x s) → x ∈ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetNoChartNull».«exists_sheet_nhds» := P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_nhds_99630c412ec0
