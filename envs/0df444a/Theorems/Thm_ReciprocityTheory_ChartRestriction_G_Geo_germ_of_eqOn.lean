-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_germ_of_eqOn
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.germ_of_eqOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:47.843021+00:00
-- url     : https://prove2.me/theorems/8785a79d-f8fe-4b1c-98ce-0ac93e2240b1
-- title:
--   Geo: germ of eq On
-- statement:
--   The Geo construction uses the germ of eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedF.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedF.lean#L80-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.germ_of_eqOn (R : AnLogRes P J e) {Q Q' : LocPot R.X}
    (h : ∀ x, ∀ y ∈ R.U x, Q.φ x y = Q'.φ x y) (j : Fin R.A.n) (y : Fin e → ℂ)
    (hy : y ∈ (R.A.chart j).target) :
    (fun y' => Q.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q'.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y') := by sorry
