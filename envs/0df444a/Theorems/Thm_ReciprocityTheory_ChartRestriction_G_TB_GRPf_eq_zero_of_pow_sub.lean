-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_eq_zero_of_pow_sub
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GRPf.eq_zero_of_pow_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:36.952396+00:00
-- url     : https://prove2.me/theorems/0153e790-aea3-4646-bf61-a21138b21a65
-- title:
--   GRPf: eq zero of pow sub
-- statement:
--   The GRPf construction uses the eq zero of pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L132-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
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
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k T : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k] [Fintype T] {rk : T → ℕ}
  (χ : T → O →+* k)

theorem ReciprocityTheory.ChartRestriction.G.TB.GRPf.eq_zero_of_pow_sub {n : ℕ} (hn : n ≠ 2) {x : k} (h : ((2 : k) ^ n - 4) * x = 0) : x = 0 := by sorry
