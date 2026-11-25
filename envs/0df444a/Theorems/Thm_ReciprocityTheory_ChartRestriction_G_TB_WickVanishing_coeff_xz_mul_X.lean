-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_xz_mul_X
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_xz_mul_X
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:38.618943+00:00
-- url     : https://prove2.me/theorems/fa25098f-27fa-4e06-b647-647260b041e1
-- title:
--   Wick Vanishing: coeff xz mul X
-- statement:
--   The Wick Vanishing construction uses the coeff xz mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L169-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L169-L185

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_xz_mul_X (φ : PS k 1 d) (j i m : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (rename (eXv d) φ * X ((1 : Fin 2), m)) =
      if m = i then coeff (single ((0 : Fin 1), j) 1) φ else 0 := by sorry
