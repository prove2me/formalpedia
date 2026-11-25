-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_not_isUnit_of_num_mem_4d37773cee31
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_not_isUnit_of_num_mem_4d37773cee31
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:15.067404+00:00
-- url     : https://prove2.me/theorems/9dc765a2-56ec-4535-b0f7-24c6449f0d4e
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds not is Unit of num mem 4d37773cee31: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds not is Unit of nu
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds not is Unit of num mem 4d37773cee31 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds not is Unit of num mem 4d37773cee31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L168-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L168-L184

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P : Ideal (MRing ι))
variable {P} [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_not_isUnit_of_num_mem_4d37773cee31 {W : Ideal (MRing ι)} (hW : W.IsPrime) (hPW : P ≤ W) {x : locRing P W}
    {u v : MRing ι} (hx : (x : FractionRing (MRing ι ⧸ P)) * frHom P v = frHom P u) (hu : u ∈ W) (hv : v ∉ W) :
    ¬ IsUnit x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«not_isUnit_of_num_mem» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_not_isUnit_of_num_mem_4d37773cee31
