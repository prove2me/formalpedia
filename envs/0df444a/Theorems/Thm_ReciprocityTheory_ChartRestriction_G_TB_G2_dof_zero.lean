-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_dof_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.dof_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:21.7478+00:00
-- url     : https://prove2.me/theorems/9ddb702d-b9aa-4e4b-8bc2-a9815bd18d47
-- title:
--   G2: dof zero
-- statement:
--   The G2 construction uses the dof zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofListSum.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofListSum.lean#L20-L21

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

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.dof_zero : Dof F v (0 : PS k 1 d) = 0 := by sorry
