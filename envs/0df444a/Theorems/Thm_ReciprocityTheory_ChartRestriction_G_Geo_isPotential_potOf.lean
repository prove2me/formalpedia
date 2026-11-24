-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isPotential_potOf
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isPotential_potOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:29.901364+00:00
-- url     : https://prove2.me/theorems/5b19091f-4a5d-4f74-a502-bf87735ddb7d
-- title:
--   Geo: is Potential pot Of
-- statement:
--   The Geo construction uses the is Potential pot Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedB.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedB.lean#L104-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.isPotential_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) := by sorry
