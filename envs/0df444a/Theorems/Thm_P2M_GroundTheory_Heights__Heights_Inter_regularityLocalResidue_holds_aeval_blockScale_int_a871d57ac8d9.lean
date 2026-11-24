-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_aeval_blockScale_int_a871d57ac8d9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_aeval_blockScale_int_a871d57ac8d9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:21.534359+00:00
-- url     : https://prove2.me/theorems/f2ba6c9a-bc29-4c98-a141-39f113cfd11c
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds aeval block Scale int a871d57ac8d9: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds aeval block Scale
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds aeval block Scale int a871d57ac8d9 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds aeval block Scale int a871d57ac8d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L43-L57

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_aeval_blockScale_int_a871d57ac8d9 {A : Type*} [CommRing A] [Algebra ℤ A] {g : MRing ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) (c : K → A) (z : (Σ k, ι k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«aeval_blockScale_int» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_aeval_blockScale_int_a871d57ac8d9
