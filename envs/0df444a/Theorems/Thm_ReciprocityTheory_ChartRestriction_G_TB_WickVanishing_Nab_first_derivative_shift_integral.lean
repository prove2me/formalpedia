-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_first_derivative_shift_integral
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.first_derivative_shift_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:49.426818+00:00
-- url     : https://prove2.me/theorems/83dfbdf7-8732-4156-ad35-9960d8f20abd
-- title:
--   Nab: first derivative shift integral
-- statement:
--   The Nab construction uses the first derivative shift integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FirstDerivativeShiftIntegral.lean#L43-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FirstDerivativeShiftIntegral.lean#L43-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
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
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.first_derivative_shift_integral {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (b : Fin d) :
    ∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b) -
      ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h) ∈ Ig R k (Fin 2 × Fin d) := by sorry
