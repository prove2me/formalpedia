-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_MV_coeff_iter_pderiv
-- name    : ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_iter_pderiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:38.048156+00:00
-- url     : https://prove2.me/theorems/833c1d69-e25b-4e4d-a308-2bdc5c9f5d56
-- title:
--   MV: coeff iter pderiv
-- statement:
--   The MV construction uses the coeff iter pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L24-L36

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
variable {k : Type} [CommRing k] {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_iter_pderiv (i : σ) (c : ℕ) (g : MvPowerSeries σ k) (n : σ →₀ ℕ) :
    coeff n ((pderiv k i)^[c] g) =
      coeff (n + c • Finsupp.single i 1) g * ((n i + 1).ascFactorial c : k) := by sorry
