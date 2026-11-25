-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fib_term
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fib_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:25.531404+00:00
-- url     : https://prove2.me/theorems/61e23647-ae02-401b-9caa-048c2c7ebcf1
-- title:
--   Geo: fib term
-- statement:
--   The Geo construction uses the fib term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeH.lean#L99-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeH.lean#L99-L161

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.fib_term (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (Pt : ChartPartition A) (g : X → ℝ) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source)
    (hxS : x ∉ S) :
    Pt.χ j ((A.chart j).symm (A.chart j x)) * g ((A.chart j).symm (A.chart j x)) *
        locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
      Pt.χ j x * (g x * pushDens A Φ q x) := by sorry
