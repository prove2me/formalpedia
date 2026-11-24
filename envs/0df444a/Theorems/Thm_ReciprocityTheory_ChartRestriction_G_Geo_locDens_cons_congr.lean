-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_locDens_cons_congr
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.locDens_cons_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:55.851109+00:00
-- url     : https://prove2.me/theorems/3f7a2fb3-1c61-4feb-a3ad-c8e7fe2e361e
-- title:
--   Geo: loc Dens cons congr
-- statement:
--   The Geo construction uses the loc Dens cons congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L72-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.locDens_cons_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    {Q Q' : LocPot X} (Φ : Fin e → LocPot X)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y'))
      =ᶠ[𝓝 y] fun y' => Q'.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    ∀ j, ∀ y ∈ (A.chart j).target,
      locDens A (Fin.cons Q Φ) j y = locDens A (Fin.cons Q' Φ) j y := by sorry
