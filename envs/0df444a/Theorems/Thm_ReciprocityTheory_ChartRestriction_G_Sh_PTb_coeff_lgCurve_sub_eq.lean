-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lgCurve_sub_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lgCurve_sub_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:35.706499+00:00
-- url     : https://prove2.me/theorems/c3142b30-a5a8-54cf-a967-6c32cb1dd59a
-- title:
--   PTb: coeff lg Curve sub eq
-- statement:
--   The PTb construction uses the coeff lg Curve sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L183-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L183-L193

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lgCurve_sub_eq (G : LogFGL v d) {α β : Fin d → PowerSeries C}
    (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (N : ℕ)
    (h : ∀ a, ∀ j < N, PowerSeries.coeff j (G.lgCurve α a) = PowerSeries.coeff j (G.lgCurve β a))
    (a : Fin d) :
    PowerSeries.coeff N (G.lgCurve α a - G.lgCurve β a) = PowerSeries.coeff N (α a - β a) := by sorry
