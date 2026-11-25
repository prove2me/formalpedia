-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cycEval_sum_smul
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval_sum_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:02.682708+00:00
-- url     : https://prove2.me/theorems/6bd42a92-06d2-4490-a1af-6d7b731180e1
-- title:
--   I1: cyc Eval sum smul
-- statement:
--   The I1 construction uses the cyc Eval sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L275-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L275-L282

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval_sum_smul (J : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ)
    (E : Ideal (MRingOver F ι) → Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (D.sum fun W m => m • E W) = cycEval (fun W => cycEval J (E W)) D := by sorry
