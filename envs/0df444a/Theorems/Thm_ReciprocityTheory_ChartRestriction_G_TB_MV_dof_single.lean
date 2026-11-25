-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_MV_dof_single
-- name    : ReciprocityTheory.ChartRestriction.G.TB.MV.dof_single
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:44.671796+00:00
-- url     : https://prove2.me/theorems/1a709639-4d51-42b9-9b5c-ba8fe9466408
-- title:
--   MV: dof single
-- statement:
--   The MV construction uses the dof single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L71-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L71-L101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.MV
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k]

theorem ReciprocityTheory.ChartRestriction.G.TB.MV.dof_single (d : ℕ) (i : Fin d) :
    (Dof (addF k d) (Pi.single i (1 : k)) : PS k 1 d → PS k 1 d) = pderiv k ((0 : Fin 1), i) := by sorry
