-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isUnit_mk_chartIdeal_X
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.isUnit_mk_chartIdeal_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:08.279808+00:00
-- url     : https://prove2.me/theorems/310f88f4-666d-49a4-a4b1-9467b43a8d02
-- title:
--   I1: is Unit mk chart Ideal X
-- statement:
--   The I1 construction uses the is Unit mk chart Ideal X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L207-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L207-L293

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.isUnit_mk_chartIdeal_X {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) (j : ∀ k, ι k)
    (p : Σ k, ι k) (hp : (X p : MRingOver F ι) ∉ V) :
    IsUnit (Ideal.Quotient.mk (chartIdeal V j) (X p)) := by sorry
