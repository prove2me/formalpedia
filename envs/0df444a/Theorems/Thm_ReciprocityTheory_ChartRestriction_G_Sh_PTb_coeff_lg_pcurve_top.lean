-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lg_pcurve_top
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lg_pcurve_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:56.174998+00:00
-- url     : https://prove2.me/theorems/ed460944-9d22-401a-bce7-70ff6ab83bc8
-- title:
--   PTb: coeff lg pcurve top
-- statement:
--   The PTb construction uses the coeff lg pcurve top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L88-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L88-L101

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lg_pcurve_top (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) :
    PowerSeries.coeff (p ^ n) (G.lgCurve (pcurve G p γ x n) a) =
      (∑ s ∈ Finset.range n, ∑ b, (x s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) a := by sorry
