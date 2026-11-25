-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lg_pcurve
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lg_pcurve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:14.25414+00:00
-- url     : https://prove2.me/theorems/f6fff4bf-e852-4efb-8c2c-4233f788d189
-- title:
--   PTb: coeff lg pcurve
-- statement:
--   The PTb construction uses the coeff lg pcurve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L12-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
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
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lg_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) (m : ℕ) :
    PowerSeries.coeff m (G.lgCurve (pcurve G p γ x n) a) = ∑ s ∈ Finset.range n, ∑ b,
      if p ^ s ∣ m then x s b ^ (m / p ^ s) * PowerSeries.coeff (m / p ^ s) (G.lgCurve (γ b) a)
      else 0 := by sorry
