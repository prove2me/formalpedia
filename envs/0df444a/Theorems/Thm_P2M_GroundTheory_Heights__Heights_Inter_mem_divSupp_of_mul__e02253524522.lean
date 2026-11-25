-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mul__e02253524522
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mul__e02253524522
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:29.087797+00:00
-- url     : https://prove2.me/theorems/92345f9d-cc3a-4e10-a457-ca90f3012269
-- title:
--   P2 M Ground Theory Heights  Heights Inter mem div Supp of mul  e02253524522: P2 M Ground Theory Heights  Heights Inter mem div Supp of mul  e02253524522
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mem div Supp of mul  e02253524522 construction uses the P2 M Ground Theory Heights  Heights Inter mem div Supp of mul  e02253524522 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L33-L36

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mul__e02253524522 {P W : Ideal (MRing ι)} {f g : MRing ι}
    (hW : W ∈ divSupp P (f * g)) (hf : f ∈ W) : W ∈ divSupp P f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mem_divSupp_of_mul'» := P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mul__e02253524522
