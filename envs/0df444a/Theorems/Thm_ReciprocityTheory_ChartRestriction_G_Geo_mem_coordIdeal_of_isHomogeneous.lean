-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_coordIdeal_of_isHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.mem_coordIdeal_of_isHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:45.486241+00:00
-- url     : https://prove2.me/theorems/b7bc321d-bb9c-4d08-ad55-d0d2d91edb24
-- title:
--   Geo: mem coord Ideal of is Homogeneous
-- statement:
--   The Geo construction uses the mem coord Ideal of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/LemCone.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/LemCone.lean#L44-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
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
open MvPolynomial
variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

theorem ReciprocityTheory.ChartRestriction.G.Geo.mem_coordIdeal_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal o x := by sorry
