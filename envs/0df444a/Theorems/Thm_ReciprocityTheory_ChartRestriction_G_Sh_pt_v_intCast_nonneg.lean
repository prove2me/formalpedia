-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_v_intCast_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_v_intCast_nonneg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:28.054077+00:00
-- url     : https://prove2.me/theorems/cd5d37ba-f3d8-58a6-96ae-961ba005b06d
-- title:
--   Sh: pt v int Cast nonneg
-- statement:
--   The Sh construction uses the pt v int Cast nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L101-L104

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_v_intCast_nonneg (n : ℤ) : (0 : WithTop ℝ) ≤ v (n : C) := by sorry
