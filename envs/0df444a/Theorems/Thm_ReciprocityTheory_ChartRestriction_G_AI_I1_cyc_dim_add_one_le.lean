-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_dim_add_one_le
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:25.822394+00:00
-- url     : https://prove2.me/theorems/728dbb19-fe85-4aef-afce-13ba50cc114a
-- title:
--   I1: cyc dim add one le
-- statement:
--   The I1 construction uses the cyc dim add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L194-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L194-L196

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le {R : Type*} [CommRing R] {P Q : Ideal R} [P.IsPrime] (hPQ : P ≤ Q)
    {x : R} (hxQ : x ∈ Q) (hxP : x ∉ P) : ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by sorry
