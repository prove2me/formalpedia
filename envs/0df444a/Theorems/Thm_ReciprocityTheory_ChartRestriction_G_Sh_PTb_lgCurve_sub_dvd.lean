-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sub_dvd
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sub_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:12.428802+00:00
-- url     : https://prove2.me/theorems/00a63793-798d-4b5c-9bf9-a4c99efb4c1d
-- title:
--   PTb: lg Curve sub dvd
-- statement:
--   The PTb construction uses the lg Curve sub dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L143-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L143-L164

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sub_dvd (G : LogFGL v d) {α β : Fin d → PowerSeries C}
    (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (k : ℕ)
    (hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ k ∣ α b - β b) (a : Fin d) :
    (PowerSeries.X : PowerSeries C) ^ (k + 1) ∣
      (G.lgCurve α a - G.lgCurve β a) - (α a - β a) := by sorry
