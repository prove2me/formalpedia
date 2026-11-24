-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_contDiffOn_potOf
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.contDiffOn_potOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:11.883568+00:00
-- url     : https://prove2.me/theorems/ccfe6a6f-c930-4fb7-8456-8582c3bc6312
-- title:
--   Geo: cont Diff On pot Of
-- statement:
--   The Geo construction uses the cont Diff On pot Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L101-L110

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.contDiffOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X)
    (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => Real.log (L.h (R.lift x ((R.A.chart j).symm y))))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by sorry
