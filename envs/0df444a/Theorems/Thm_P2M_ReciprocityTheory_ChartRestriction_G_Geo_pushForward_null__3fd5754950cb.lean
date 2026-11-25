-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_pushForward_null__3fd5754950cb
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_pushForward_null__3fd5754950cb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:20.244644+00:00
-- url     : https://prove2.me/theorems/613425e7-3865-5330-8757-66c337a2858c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo push Forward null  3fd5754950cb: P2 M Reciprocity Theory Chart Restriction G Geo push Forward null  3fd5754950cb
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo push Forward null  3fd5754950cb construction uses the P2 M Reciprocity Theory Chart Restriction G Geo push Forward null  3fd5754950cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeI.lean#L11-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeI.lean#L11-L90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeI
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
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_pushForward_null__3fd5754950cb [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«pushForward_null'» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_pushForward_null__3fd5754950cb
