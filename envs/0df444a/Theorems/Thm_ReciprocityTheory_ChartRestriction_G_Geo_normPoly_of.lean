-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_normPoly_of
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.normPoly_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:36.018649+00:00
-- url     : https://prove2.me/theorems/08e4ee8d-4b80-5bf1-8c7f-2a992174ce82
-- title:
--   Geo: norm Poly of
-- statement:
--   The Geo construction uses the norm Poly of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeQ.lean#L110-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeQ.lean#L110-L211

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.normPoly_of (hM : PCMinContractStatement) : NormPolyStatement := by sorry
