-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ad_side1
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ad_side1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:55.191793+00:00
-- url     : https://prove2.me/theorems/d765dab5-efdf-4204-8062-4c16fd71bf0b
-- title:
--   Wick Vanishing: coeff ad side1
-- statement:
--   The Wick Vanishing construction uses the coeff ad side1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L210-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L210-L228

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
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
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ad_side1 (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1)
        (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h) =
      ∑ l, coeff (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), i) 1) h * dAct k B a l j := by sorry
