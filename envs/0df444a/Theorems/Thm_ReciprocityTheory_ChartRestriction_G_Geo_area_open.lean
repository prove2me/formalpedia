-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_area_open
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.area_open
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:10.155768+00:00
-- url     : https://prove2.me/theorems/59738cbe-72fd-4d4f-a5e1-bc43554b23bf
-- title:
--   Geo: area open
-- statement:
--   The Geo construction uses the area open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L173-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L173-L205

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
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
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.area_open {O : Set (Fin e → ℂ)} (hO : IsOpen O) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : IntegrableOn h O) (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) :
    Integrable (fibSum O Q h) ∧ ∫ u in O, h u = ∫ y, fibSum O Q h y := by sorry
