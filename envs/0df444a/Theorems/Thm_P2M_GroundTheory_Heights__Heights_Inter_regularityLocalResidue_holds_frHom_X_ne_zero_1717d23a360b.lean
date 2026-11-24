-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_X_ne_zero_1717d23a360b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_X_ne_zero_1717d23a360b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:13.226269+00:00
-- url     : https://prove2.me/theorems/d2d1b678-0159-4399-9729-cedddd29f317
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom X ne zero 1717d23a360b: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom X ne zero 1717d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom X ne zero 1717d23a360b construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom X ne zero 1717d23a360b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L212-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L212-L214

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_X_ne_zero_1717d23a360b {W : Ideal (MRing ι)} (hPW : P ≤ W) {T : ∀ k, ι k}
    (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W) (k : K) : frHom P (X ⟨k, T k⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«frHom_X_ne_zero» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_X_ne_zero_1717d23a360b
