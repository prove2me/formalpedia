-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_low_of_lin
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_low_of_lin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:15.055857+00:00
-- url     : https://prove2.me/theorems/31650b10-51f8-5c8d-91f0-a86bd54ae6c6
-- title:
--   Sh: pt low of lin
-- statement:
--   The Sh construction uses the pt low of lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L47-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L47-L77

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_low_of_lin {σ : Type*} [Fintype σ] {Φ : MvPowerSeries σ C}
    (h0 : constantCoeff Φ = 0) (m : σ → C)
    (hm : ∀ s, coeff (Finsupp.single s 1) Φ = m s) :
    ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α (Φ - ∑ a, m a • X a) = 0 := by sorry
