-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_arithmeticPoincareLelong_of
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.arithmeticPoincareLelong_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:30.358227+00:00
-- url     : https://prove2.me/theorems/3213dda0-9213-4db8-96e7-b552c23caa26
-- title:
--   Geo: arithmetic Poincare Lelong of
-- statement:
--   The Geo construction uses the arithmetic Poincare Lelong of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L129-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean#L129-L183

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.arithmeticPoincareLelong_of (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) (hPL : ReciprocityTheory.AnForm.M.PoincareLelongStatement)
    (hInd : ReciprocityTheory.AnForm.M.SNCInducedAtlasStatement) (hPush : ResDivPushStatement) :
    ArithmeticPoincareLelongFormula := by sorry
