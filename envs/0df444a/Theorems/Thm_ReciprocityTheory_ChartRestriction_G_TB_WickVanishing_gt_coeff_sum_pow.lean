-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_coeff_sum_pow
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_sum_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:25.325538+00:00
-- url     : https://prove2.me/theorems/2393bedc-25f1-4f87-95e1-a9287090a03a
-- title:
--   Wick Vanishing: gt coeff sum pow
-- statement:
--   The Wick Vanishing construction uses the gt coeff sum pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L40-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L40-L76

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
variable (A : Type) [CommRing A] [Algebra ℚ A]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_sum_pow (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e (((X 0 : MvPowerSeries (Fin 2) A) + X 1) ^ n) =
      if e 0 + e 1 = n then ((n.choose (e 0) : ℕ) : A) else 0 := by sorry
