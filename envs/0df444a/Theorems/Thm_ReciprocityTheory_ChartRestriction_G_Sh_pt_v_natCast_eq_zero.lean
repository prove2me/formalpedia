-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_v_natCast_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_v_natCast_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:14.228653+00:00
-- url     : https://prove2.me/theorems/608add95-409a-45cf-aadb-39d5adeaaf91
-- title:
--   Sh: pt v nat Cast eq zero
-- statement:
--   The Sh construction uses the pt v nat Cast eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L106-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L106-L123

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_v_natCast_eq_zero {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) {n : ℕ}
    (hn : ¬ p ∣ n) : v (n : C) = 0 := by sorry
