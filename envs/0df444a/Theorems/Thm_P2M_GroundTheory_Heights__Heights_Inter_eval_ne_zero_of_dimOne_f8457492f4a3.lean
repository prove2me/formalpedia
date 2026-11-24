-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_eval_ne_zero_of_dimOne_f8457492f4a3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_eval_ne_zero_of_dimOne_f8457492f4a3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:14.907026+00:00
-- url     : https://prove2.me/theorems/9effee34-7b37-4f7e-9c52-8ca892f8f5ec
-- title:
--   P2 M Ground Theory Heights  Heights Inter eval ne zero of dim One f8457492f4a3: P2 M Ground Theory Heights  Heights Inter eval ne zero of dim One f8457492f4a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter eval ne zero of dim One f8457492f4a3 construction uses the P2 M Ground Theory Heights  Heights Inter eval ne zero of dim One f8457492f4a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L109-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L109-L136

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

theorem P2M_GroundTheory_Heights__Heights_Inter_eval_ne_zero_of_dimOne_f8457492f4a3 (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : eval z (map (Int.castRingHom ℂ) s) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«eval_ne_zero_of_dimOne» := P2M_GroundTheory_Heights__Heights_Inter_eval_ne_zero_of_dimOne_f8457492f4a3
