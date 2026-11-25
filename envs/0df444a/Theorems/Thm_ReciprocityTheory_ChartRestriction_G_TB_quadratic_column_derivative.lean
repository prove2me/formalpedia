-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_quadratic_column_derivative
-- name    : ReciprocityTheory.ChartRestriction.G.TB.quadratic_column_derivative
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:58.901945+00:00
-- url     : https://prove2.me/theorems/ba92649a-5873-444e-98de-e23f9bf0a6ae
-- title:
--   TB: quadratic column derivative
-- statement:
--   The TB construction uses the quadratic column derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAddQ.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAddQ.lean#L61-L79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB

theorem ReciprocityTheory.ChartRestriction.G.TB.quadratic_column_derivative : QuadColDerivSt := by sorry
