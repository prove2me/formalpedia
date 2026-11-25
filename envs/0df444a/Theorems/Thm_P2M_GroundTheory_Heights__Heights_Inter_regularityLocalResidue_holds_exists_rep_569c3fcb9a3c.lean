-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_exists_rep_569c3fcb9a3c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_exists_rep_569c3fcb9a3c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:42.930805+00:00
-- url     : https://prove2.me/theorems/67b19539-37cd-4230-8641-088d5db5c3c5
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds exists rep 569c3fcb9a3c: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds exists rep 569c3fcb9a3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds exists rep 569c3fcb9a3c construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds exists rep 569c3fcb9a3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L139-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L139-L166

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_exists_rep_569c3fcb9a3c {W : Ideal (MRing ι)} (hW : W.IsPrime) {x : FractionRing (MRing ι ⧸ P)}
    (hx : x ∈ locRing P W) :
    ∃ (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ x * frHom P v = frHom P u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«exists_rep» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_exists_rep_569c3fcb9a3c
