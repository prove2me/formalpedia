-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_exists_monomial_not_mem
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.exists_monomial_not_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:07.812796+00:00
-- url     : https://prove2.me/theorems/ef5603c0-85cd-4905-b3cf-74a8c5a7b37a
-- title:
--   I1: exists monomial not mem
-- statement:
--   The I1 construction uses the exists monomial not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/ExistsMonomialNotMem.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/ExistsMonomialNotMem.lean#L103-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.exists_monomial_not_mem {W : Ideal (MRingOver F ι)} (hW : W.IsPrime) (hr : IsRelevant W)
    (d : K → ℕ) : ∃ f : MRingOver F ι, IsMultiHomog f d ∧ f ∉ W := by sorry
