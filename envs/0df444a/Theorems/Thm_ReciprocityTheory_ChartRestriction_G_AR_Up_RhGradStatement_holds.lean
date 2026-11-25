-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RhGradStatement_holds
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.RhGradStatement_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:10.59261+00:00
-- url     : https://prove2.me/theorems/66d3d000-5c91-58b5-9df2-eb6ded880d7f
-- title:
--   Up: Rh Grad Statement holds
-- statement:
--   The Up construction uses the Rh Grad Statement holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPf.lean#L174-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPf.lean#L174-L187

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.RhGradStatement_holds : RhGradStatement := by sorry
