-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_eq_of_point_le
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_point_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:52.274321+00:00
-- url     : https://prove2.me/theorems/4d93e1c1-8749-4fdc-806f-b2ee004d1f46
-- title:
--   I1: eq of point le
-- statement:
--   The I1 construction uses the eq of point le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L387-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L387-L410

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_point_le {P : Ideal (MRingOver F ι)} (hW : IsProjVarF W 0) (hP : P.IsPrime)
    (hPh : IsMultiHomogIdeal P) {j : ∀ k, ι k} (hj : IsChart P j) (hWP : W ≤ P) : P = W := by sorry
