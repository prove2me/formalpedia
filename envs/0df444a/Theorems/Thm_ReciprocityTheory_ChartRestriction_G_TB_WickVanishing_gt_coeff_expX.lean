-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_coeff_expX
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_expX
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:38.761305+00:00
-- url     : https://prove2.me/theorems/0ea58e17-468b-4ac5-9cfd-ee8fc2a446d3
-- title:
--   Wick Vanishing: gt coeff exp X
-- statement:
--   The Wick Vanishing construction uses the gt coeff exp X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L22-L34

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_coeff_expX (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) A) (PowerSeries.exp A)) =
      if e = single i (e i) then algebraMap ℚ A (1 / (e i).factorial) else 0 := by sorry
