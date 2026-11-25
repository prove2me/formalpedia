-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_mvIsInt_subst
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:13.309186+00:00
-- url     : https://prove2.me/theorems/74da10ae-8371-4310-baf2-811059decbd2
-- title:
--   PTb: mv Is Int subst
-- statement:
--   The PTb construction uses the mv Is Int subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L32-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L32-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst {σ τ : Type} [Finite σ] (v : AddValuation C (WithTop ℝ))
    {f : MvPowerSeries σ C} (hf : MvIsInt v f) {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvIsInt v (a s)) (ha0 : ∀ s, constantCoeff (a s) = 0) :
    MvIsInt v (subst a f) := by sorry
