-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_locDens_congr_of_eqOn
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.locDens_congr_of_eqOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:48.634137+00:00
-- url     : https://prove2.me/theorems/d89c5002-807f-53b1-b6c1-245bbf17f0c9
-- title:
--   Geo: loc Dens congr of eq On
-- statement:
--   The Geo construction uses the loc Dens congr of eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedF.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedF.lean#L91-L98

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.locDens_congr_of_eqOn (R : AnLogRes P J e) {Φ Φ' : Fin e → LocPot R.X}
    (h : ∀ i x, ∀ y ∈ R.U x, (Φ i).φ x y = (Φ' i).φ x y) :
    ∀ j, ∀ y ∈ (R.A.chart j).target, locDens R.A Φ j y = locDens R.A Φ' j y := by sorry
