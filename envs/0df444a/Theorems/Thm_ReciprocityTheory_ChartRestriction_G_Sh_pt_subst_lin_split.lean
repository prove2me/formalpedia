-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_subst_lin_split
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_subst_lin_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:29.937537+00:00
-- url     : https://prove2.me/theorems/cbfd51d0-86ac-4c8c-a770-9cbeb76ff207
-- title:
--   Sh: pt subst lin split
-- statement:
--   The Sh construction uses the pt subst lin split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L37-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
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
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_subst_lin_split {σ τ : Type*} [Fintype σ] {x : σ → MvPowerSeries τ C}
    (hx : HasSubst x) (Φ : MvPowerSeries σ C) (m : σ → C) :
    subst x Φ = ∑ a, m a • x a + subst x (Φ - ∑ a, m a • X a) := by sorry
