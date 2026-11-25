-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_hK_of_low
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_hK_of_low
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:00.311293+00:00
-- url     : https://prove2.me/theorems/35df19bb-5095-4a3f-9526-f5b5fe7b4f69
-- title:
--   Sh: pt h K of low
-- statement:
--   The Sh construction uses the pt h K of low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L264-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L264-L270

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
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_hK_of_low {σ τ : Type*} {K : MvPowerSeries σ R}
    (hK : ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α K = 0) (A A' : σ → MvPowerSeries τ R) :
    ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s := by sorry
