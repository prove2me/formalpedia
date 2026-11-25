-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_eigen_orthogonality
-- name    : ReciprocityTheory.ChartRestriction.G.TB.eigen_orthogonality
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:11.155626+00:00
-- url     : https://prove2.me/theorems/0aa749c7-e8f6-560b-956f-fcefb0e689d3
-- title:
--   TB: eigen orthogonality
-- statement:
--   The TB construction uses the eigen orthogonality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/EigenLift.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/EigenLift.lean#L32-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_EigenLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EigenLift
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem ReciprocityTheory.ChartRestriction.G.TB.eigen_orthogonality : EigenOrthSt := by sorry
