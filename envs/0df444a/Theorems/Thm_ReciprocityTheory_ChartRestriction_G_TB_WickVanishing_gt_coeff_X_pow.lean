-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_coeff_X_pow
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_X_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:44.110433+00:00
-- url     : https://prove2.me/theorems/980c8c99-ae25-59bb-abb2-25d7cb132c40
-- title:
--   Wick Vanishing: gt coeff X pow
-- statement:
--   The Wick Vanishing construction uses the gt coeff X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L15-L20

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_X_pow (i : Fin 2) (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X i : MvPowerSeries (Fin 2) A) ^ n) = if e = single i n then 1 else 0 := by sorry
