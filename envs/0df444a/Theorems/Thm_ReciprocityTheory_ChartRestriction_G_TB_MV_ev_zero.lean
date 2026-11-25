-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_MV_ev_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.MV.ev_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:02.146343+00:00
-- url     : https://prove2.me/theorems/b00c7090-4303-5d39-8759-78239e29d1ea
-- title:
--   MV: ev zero
-- statement:
--   The MV construction uses the ev zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L66-L69

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

theorem ReciprocityTheory.ChartRestriction.G.TB.MV.ev_zero {d m n : ℕ} (a : Fin m → Pt k n d) : ev a (0 : PS k m d) = 0 := by sorry
