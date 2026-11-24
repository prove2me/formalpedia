-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_not_isHorizontal_of_dimOne_554e14cba4bd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_not_isHorizontal_of_dimOne_554e14cba4bd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:46.755964+00:00
-- url     : https://prove2.me/theorems/cdb17b00-6e12-42a9-8966-28c1b245fd1d
-- title:
--   P2 M Ground Theory Heights  Heights Inter not is Horizontal of dim One 554e14cba4bd: P2 M Ground Theory Heights  Heights Inter not is Horizontal of dim One 554e14cba4bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter not is Horizontal of dim One 554e14cba4bd construction uses the P2 M Ground Theory Heights  Heights Inter not is Horizontal of dim One 554e14cba4bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L104-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_not_isHorizontal_of_dimOne_554e14cba4bd (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} {W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hs : IsSectionOn P A s)
    (hW : W ∈ divSupp P s) : ¬ IsHorizontal W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«not_isHorizontal_of_dimOne» := P2M_GroundTheory_Heights__Heights_Inter_not_isHorizontal_of_dimOne_554e14cba4bd
