-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_of_dimOne_5c38e96ea71e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_of_dimOne_5c38e96ea71e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:19.758254+00:00
-- url     : https://prove2.me/theorems/a874e78a-f38c-4527-9f80-c6e8598c3741
-- title:
--   P2 M Ground Theory Heights  Heights Inter ar Int mul of dim One 5c38e96ea71e: P2 M Ground Theory Heights  Heights Inter ar Int mul of dim One 5c38e96ea71e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ar Int mul of dim One 5c38e96ea71e construction uses the P2 M Ground Theory Heights  Heights Inter ar Int mul of dim One 5c38e96ea71e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L164-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L164-L178

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

theorem P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_of_dimOne_5c38e96ea71e (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {A B : HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) (Fin.elim0 : Fin 0 → HermLine ι) =
      arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) + arInt P t B (Fin.elim0 : Fin 0 → HermLine ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«arInt_mul_of_dimOne» := P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_of_dimOne_5c38e96ea71e
