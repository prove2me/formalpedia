-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptGood_lim
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptGood_lim
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:29.991381+00:00
-- url     : https://prove2.me/theorems/2d9099f9-6cef-4b07-a1a4-4014cbaf7322
-- title:
--   Sh: pt Good lim
-- statement:
--   The Sh construction uses the pt Good lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L21-L35

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptGood_lim {ι τ : Type*} {T : (ι → MvPowerSeries τ C) → (ι → MvPowerSeries τ C)}
    (hP : ∀ n, PTGood v (T^[n] 0)) (x : ι → MvPowerSeries τ C)
    (hx : ∀ n, PTAgree n x (T^[n] 0)) : PTGood v x := by sorry
