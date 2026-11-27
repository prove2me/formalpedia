-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_point_hilb
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.point_hilb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:00.261787+00:00
-- url     : https://prove2.me/theorems/c0787a10-4241-4b52-a7e9-581de9a3e32a
-- title:
--   I1: point hilb
-- statement:
--   The I1 construction uses the point hilb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L355-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L355-L385

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {W : Ideal (MRingOver F ι)}

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.point_hilb [DecidableEq K] (hW : IsProjVarF W 0) {j : ∀ k, ι k} (hj : IsChart W j) :
    ∃ e₀ : K → ℕ, ∀ e, e₀ ≤ e →
      Module.finrank F ↥(weightedHomogeneousSubmodule F (mw (ι := ι)) e ⊓ W.restrictScalars F) +
        ptDeg W j = Module.finrank F ↥(weightedHomogeneousSubmodule F (mw (ι := ι)) e) := by sorry
