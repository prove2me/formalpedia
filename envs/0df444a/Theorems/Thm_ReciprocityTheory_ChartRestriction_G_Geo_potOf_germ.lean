-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_potOf_germ
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.potOf_germ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:47.673801+00:00
-- url     : https://prove2.me/theorems/a8ce71e1-f3a5-496c-9474-f4ffd6df8d9e
-- title:
--   Geo: pot Of germ
-- statement:
--   The Geo construction uses the pot Of germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L129-L140

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
variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.potOf_germ (R : AnLogRes P J e) {B : HermLine ι} (hB0 : B.a = 0) (j : Fin R.A.n)
    (y : Fin e → ℂ) (hy : y ∈ (R.A.chart j).target) :
    (fun y' => (potOf R B).φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => (LocPot.ofFun fun x => Real.log (B.h (R.lift x x))).φ ((R.A.chart j).symm y)
        ((R.A.chart j).symm y') := by sorry
