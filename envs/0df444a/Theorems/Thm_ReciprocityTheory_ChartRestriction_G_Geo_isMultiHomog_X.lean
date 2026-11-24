-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_X
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:28.475889+00:00
-- url     : https://prove2.me/theorems/c09c2ccc-7fa6-4519-b500-45dc9abe4e83
-- title:
--   Geo: is Multi Homog X
-- statement:
--   The Geo construction uses the is Multi Homog X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L10-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
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
open MvPolynomial ReciprocityTheory.AnForm.M

theorem ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) :
    IsMultiHomog (X q : MRing ι) (fun k => ∑ i, (Finsupp.single q 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩) := by sorry
