-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_toPotentialCharts_07629cb4ee2b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_toPotentialCharts_07629cb4ee2b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:49.159839+00:00
-- url     : https://prove2.me/theorems/922907b4-5e00-51c8-bd56-871b5766ebf9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Is Cutoff Family to Potential Charts 07629cb4ee2b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Is Cutoff Family to Potential Charts 07629cb4ee2b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Is Cutoff Family to Potential Charts 07629cb4ee2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ToPotentialChartsChartFun.lean#L214-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ToPotentialChartsChartFun.lean#L214-L233

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__integral_37214bfa7034
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_toPotentialCharts_07629cb4ee2b [T2Space X] {R : RegCharts A} {hW : ∀ j, R.W j ⊆ ball 0 1}
    {C : ℝ} {η : Fin R.n → X → ℝ} (hη : R.IsCutoffFamily C η) (j : Fin R.n) :
    let P := R.toPotentialCharts hW
    A.SmoothOn (P.mid j) (η j) ∧ (∀ x ∈ P.mid j, -1 ≤ η j x ∧ η j x ≤ 0) ∧
      (∀ x ∈ P.inner j, η j x = 0) ∧
      ∃ L : Set X, IsClosed L ∧ L ⊆ P.mid j ∧ ∀ x ∈ P.mid j \ L, η j x = -1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«IsCutoffFamily».«toPotentialCharts» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_toPotentialCharts_07629cb4ee2b
