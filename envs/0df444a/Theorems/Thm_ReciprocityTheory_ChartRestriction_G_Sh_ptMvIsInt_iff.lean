-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptMvIsInt_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptMvIsInt_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:21.966737+00:00
-- url     : https://prove2.me/theorems/1adc1b6b-89a1-5001-9b92-27bb63c91116
-- title:
--   Sh: pt Mv Is Int iff
-- statement:
--   The Sh construction uses the pt Mv Is Int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L43-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L43-L43

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptMvIsInt_iff {σ : Type*} (f : MvPowerSeries σ C) : MvIsInt v f ↔ f ∈ ptIntSer v σ := by sorry
