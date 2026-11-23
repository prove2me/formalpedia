-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_X
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:48.335605+00:00
-- url     : https://prove2.me/theorems/cbb0ff77-99fa-41c2-bbe1-535374022c79
-- title:
--   Sh: pt Int Ser X
-- statement:
--   The Sh construction uses the pt Int Ser X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L60-L65

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer_X {σ : Type*} (s : σ) : (X s : MvPowerSeries σ C) ∈ ptIntSer v σ := by sorry
