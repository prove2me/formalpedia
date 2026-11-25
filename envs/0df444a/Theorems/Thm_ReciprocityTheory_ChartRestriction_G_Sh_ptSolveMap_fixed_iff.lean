-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSolveMap_fixed_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptSolveMap_fixed_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:18.748347+00:00
-- url     : https://prove2.me/theorems/dd95d682-7ed4-452d-a541-581f644dcf70
-- title:
--   Sh: pt Solve Map fixed iff
-- statement:
--   The Sh construction uses the pt Solve Map fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L100-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean#L100-L117

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
variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptSolveMap_fixed_iff (hNM : N * M = 1) (hMN : M * N = 1)
    (x : Fin d → MvPowerSeries τ C) :
    ptSolveMap A K N f x = x ↔ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by sorry
