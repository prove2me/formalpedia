-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_resDivPush_of_fibre
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.resDivPush_of_fibre
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:50.28986+00:00
-- url     : https://prove2.me/theorems/18142bc2-eb17-4394-a76d-01e89540abda
-- title:
--   Geo: res Div Push of fibre
-- statement:
--   The Geo construction uses the res Div Push of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushA.lean#L79-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushA.lean#L79-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

theorem ReciprocityTheory.ChartRestriction.G.Geo.resDivPush_of_fibre (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hI : PtsIntegrableStatement) (hC : DivPushCommonProjStatement)
    (hF : DivPushFibreStatement) : ResDivPushStatement := by sorry
