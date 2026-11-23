-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_subst
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:27.677509+00:00
-- url     : https://prove2.me/theorems/b0f548ea-a95e-4862-a4d4-27865fa04067
-- title:
--   Sh: pt Int Ser subst
-- statement:
--   The Sh construction uses the pt Int Ser subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L73-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L73-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer_subst {σ τ : Type*} {A : σ → MvPowerSeries τ C} (hA : HasSubst A)
    (hAi : ∀ s, A s ∈ ptIntSer v τ) {f : MvPowerSeries σ C} (hf : f ∈ ptIntSer v σ) :
    subst A f ∈ ptIntSer v τ := by sorry
