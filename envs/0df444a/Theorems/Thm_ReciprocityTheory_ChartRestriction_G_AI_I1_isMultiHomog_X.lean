-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_X
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:49.117814+00:00
-- url     : https://prove2.me/theorems/8528afac-9ade-41ec-9b2d-62093e5e0adf
-- title:
--   I1: is Multi Homog X
-- statement:
--   The I1 construction uses the is Multi Homog X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/ExistsMonomialNotMem.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/ExistsMonomialNotMem.lean#L26-L36

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
open Classical

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver F ι) (Pi.single k 1) := by sorry
