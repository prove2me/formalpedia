-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:35.65903+00:00
-- url     : https://prove2.me/theorems/5e46a70a-79b2-4daa-a613-f03ab7026813
-- title:
--   Wick Vanishing: single point zero constant
-- statement:
--   The Wick Vanishing construction uses the single point zero constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L258-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L258-L263

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant {n : ℕ} {a : Pt k n d} (ha : GP a) : ∀ j, GP (![a] j) := by sorry
