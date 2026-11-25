-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_type
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_type
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:31.952134+00:00
-- url     : https://prove2.me/theorems/b88e378e-121b-4cb1-a95a-90c7261ef6c4
-- title:
--   PTb: ptx type
-- statement:
--   The PTb construction uses the ptx type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L179-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CoeffLgPcurveTop.lean#L179-L214

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_type {h : ℕ} (ty : Fin d → ZMod h) (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0)
    (hγty : ∀ b, G.IsOfType p ty (ty b) (γ b)) (ga : Fin d → PowerSeries C) (i : ZMod h)
    (hga : G.IsOfType p ty i ga) :
    ∀ n b, ptx G p γ ga n b ≠ 0 → ty b = i + n := by sorry
