-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lg_agree
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.lg_agree
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:47.469097+00:00
-- url     : https://prove2.me/theorems/7875be9c-0585-5f67-9c75-2f474d1e34bd
-- title:
--   PTb: lg agree
-- statement:
--   The PTb construction uses the lg agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L26-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L26-L86

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.lg_agree (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hγt : ∀ b, G.IsPTypical p (γ b)) (hdet : v (tmat γ).det = 0)
    (ga : Fin d → PowerSeries C) (hga : G.IsPTypical p ga) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (ptx G p γ ga s b)) :
    ∀ a, ∀ j < p ^ n, PowerSeries.coeff j (G.lgCurve ga a) =
      PowerSeries.coeff j (G.lgCurve (pcurve G p γ (ptx G p γ ga) n) a) := by sorry
