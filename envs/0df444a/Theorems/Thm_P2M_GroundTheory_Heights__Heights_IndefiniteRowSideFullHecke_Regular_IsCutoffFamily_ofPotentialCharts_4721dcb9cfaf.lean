-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_ofPotentialCharts_4721dcb9cfaf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_ofPotentialCharts_4721dcb9cfaf
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:03.073587+00:00
-- url     : https://prove2.me/theorems/0598d4ff-a413-52ce-9eef-e09229a35ead
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Is Cutoff Family of Potential Charts 4721dcb9cfaf: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Is Cutoff Family of Potential Charts 4721dcb9cfaf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Is Cutoff Family of Potential Charts 4721dcb9cfaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ToPotentialChartsChartFun.lean#L191-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ToPotentialChartsChartFun.lean#L191-L212

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_ofPotentialCharts_4721dcb9cfaf [CompactSpace X] {P : PotentialCharts A} {om : LocPot X}
    {om_pot : IsPotential A om} {om_pos : IsPosPot A om} {η : Fin P.N → X → ℝ} {Cη : ℝ}
    (hη : P.IsCutoffFamily η Cη) (j : Fin P.N) :
    let R := RegCharts.ofPotentialCharts P om om_pot om_pos
    A.SmoothOn (R.V' j) (η j) ∧ (∀ x ∈ R.V' j, -1 ≤ η j x ∧ η j x ≤ 0) ∧
      (∀ x ∈ R.V'' j, η j x = 0) ∧
      ∃ K : Set (Fin D → ℂ), IsCompact K ∧ K ⊆ R.W' j ∧ ∀ x ∈ R.V' j, R.ψ j x ∉ K → η j x = -1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«IsCutoffFamily».«ofPotentialCharts» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_ofPotentialCharts_4721dcb9cfaf
