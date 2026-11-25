-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cz0z
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cz0z
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:39.104108+00:00
-- url     : https://prove2.me/theorems/7fe5294e-b892-4f85-91e5-4313a94e5789
-- title:
--   Nab: cz0z
-- statement:
--   The Nab construction uses the cz0z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/IntegralFamilyFirstZeroSecond.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/IntegralFamilyFirstZeroSecond.lean#L21-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cz0z : CZ (![pt k (n := 2) d 0, 0, pt k d 1] : Fin 3 → Pt k 2 d) := by sorry
