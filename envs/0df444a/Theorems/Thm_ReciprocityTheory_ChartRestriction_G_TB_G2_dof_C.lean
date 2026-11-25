-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_dof_C
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.dof_C
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:09.146283+00:00
-- url     : https://prove2.me/theorems/5e2f0fff-f1fb-5095-8edd-12ccf6b68d8c
-- title:
--   G2: dof C
-- statement:
--   The G2 construction uses the dof C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofListSum.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofListSum.lean#L23-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) (v : Fin d → k)

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.dof_C (a : k) : Dof F v (C a : PS k 1 d) = 0 := by sorry
