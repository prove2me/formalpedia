-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_eventuallyEq_comp_chart_de7d972882f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_eventuallyEq_comp_chart_de7d972882f5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:16.02343+00:00
-- url     : https://prove2.me/theorems/f152cf2d-991f-459b-82c2-575ee1198e5a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Levi Th Ge eventually Eq comp chart de7d972882f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Re
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Levi Th Ge eventually Eq comp chart de7d972882f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Levi Th Ge eventually Eq comp chart de7d972882f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartLeviThGe.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartLeviThGe.lean#L26-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartLeviThGe
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_analyticAt_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero

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
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (contDiffOn_compat analyticAt_compat)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_eventuallyEq_comp_chart_de7d972882f5 {β : Type*} (h : X → β) (ψ χ : OpenPartialHomeomorph X (Fin D → ℂ))
    {y : Fin D → ℂ} (hy : y ∈ χ.target) (hs : χ.symm y ∈ ψ.source) :
    h ∘ χ.symm =ᶠ[𝓝 y] (h ∘ ψ.symm) ∘ (ψ ∘ χ.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«ChartLeviThGe».«eventuallyEq_comp_chart» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_eventuallyEq_comp_chart_de7d972882f5
