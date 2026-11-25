-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomogIdeal_span_X
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_span_X
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:10.919926+00:00
-- url     : https://prove2.me/theorems/3bfe9cdc-46c0-489a-bdcd-12fd4c2dcc49
-- title:
--   Geo: is Multi Homog Ideal span X
-- statement:
--   The Geo construction uses the is Multi Homog Ideal span X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L18-L22

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_span_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) : IsMultiHomogIdeal (Ideal.span {(X q : MRing ι)}) := by sorry
