-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_pos_compat_1b0edf5128a1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_pos_compat_1b0edf5128a1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:59:46.701615+00:00
-- url     : https://prove2.me/theorems/f8bfa34c-3f76-4c99-9a9d-069c0bf9f688
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Levi Th Ge levi pos compat 1b0edf5128a1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Cha
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Levi Th Ge levi pos compat 1b0edf5128a1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Chart Levi Th Ge levi pos compat 1b0edf5128a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartLeviThGe.lean#L103-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartLeviThGe.lean#L103-L118

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
variable {om : LocPot X}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_pos_compat_1b0edf5128a1 (hpot : IsPotential A om) (hpos : IsPosPot A om)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {x p : X}
    (hpx : p ∈ om.U x) (hpψ : p ∈ ψ.source) {v : Fin D → ℂ} (hv : v ≠ 0) :
    0 < levi (om.φ x ∘ ψ.symm) (ψ p) v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«ChartLeviThGe».«levi_pos_compat» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_pos_compat_1b0edf5128a1
