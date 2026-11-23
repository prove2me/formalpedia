-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_expand_rescale
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_expand_rescale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:56.471056+00:00
-- url     : https://prove2.me/theorems/2e49859f-65d0-46ec-b0ad-b903358d91ea
-- title:
--   PTb: coeff expand rescale
-- statement:
--   The PTb construction uses the coeff expand rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L244-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L244-L250

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_expand_rescale (q : ℕ) (hq : q ≠ 0) (x : C) (f : PowerSeries C) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.expand q hq (PowerSeries.rescale x f)) =
      if q ∣ m then x ^ (m / q) * PowerSeries.coeff (m / q) f else 0 := by sorry
