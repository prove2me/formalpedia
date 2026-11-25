-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchChartInt_integrableOn_branch_510bf2dc1691
-- name    : P2M_GroundTheory_Heights__Heights_BranchChartInt_integrableOn_branch_510bf2dc1691
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:12.623803+00:00
-- url     : https://prove2.me/theorems/425ad1db-d229-40f7-84ce-baede2587edc
-- title:
--   P2 M Ground Theory Heights  Heights Branch Chart Int integrable On branch 510bf2dc1691: P2 M Ground Theory Heights  Heights Branch Chart Int integrable On branch 510bf2dc1691
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch Chart Int integrable On branch 510bf2dc1691 construction uses the P2 M Ground Theory Heights  Heights Branch Chart Int integrable On branch 510bf2dc1691 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L105-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchChartInt
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.BranchChartInt

theorem P2M_GroundTheory_Heights__Heights_BranchChartInt_integrableOn_branch_510bf2dc1691 {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : VarBranch J d p) {g : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hg : Continuous g)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    (hK : ∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ Metric.ball 0 γ.radius ∧
      ∀ t ∈ Metric.ball 0 γ.radius, t ∉ K → g (γ.toFun t) = 0) :
    IntegrableOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchChartInt».«integrableOn_branch» := P2M_GroundTheory_Heights__Heights_BranchChartInt_integrableOn_branch_510bf2dc1691
