-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_secSet_of_sheet
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.mem_secSet_of_sheet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:53.743402+00:00
-- url     : https://prove2.me/theorems/cd449397-2589-40a0-9dad-7cb71109cc71
-- title:
--   Geo: mem sec Set of sheet
-- statement:
--   The Geo construction uses the mem sec Set of sheet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetB.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetB.lean#L99-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.mem_secSet_of_sheet {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {B : Set (Fin e → ℂ)}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : ∀ y' ∈ B, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y') :
    B.indicator (fun y' => segre (γ y')) ∈ secSet P Ψ B := by sorry
