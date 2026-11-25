-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_stokes_of
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.stokes_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:30.044876+00:00
-- url     : https://prove2.me/theorems/1d22f9cd-7778-50bc-8625-cc95c34b3587
-- title:
--   Geo: stokes of
-- statement:
--   The Geo construction uses the stokes of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L100-L108

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.stokes_of (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) (hBP : ReciprocityTheory.AnForm.M.ByPartsSymmStatement)
    (hPot : PotOfPotentialStatement) : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by sorry
