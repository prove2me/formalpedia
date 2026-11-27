-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_smoothOn_potOf
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.smoothOn_potOf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:26.993306+00:00
-- url     : https://prove2.me/theorems/3d867a1b-0879-4ed1-823b-3eb30c1c5a40
-- title:
--   Geo: smooth On pot Of
-- statement:
--   The Geo construction uses the smooth On pot Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L112-L113

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.smoothOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X) :
    R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := by sorry
