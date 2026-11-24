-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_eq_zero_iff_cc85a26563f0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_eq_zero_iff_cc85a26563f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:36.956422+00:00
-- url     : https://prove2.me/theorems/00674488-3066-4edb-8b16-09f481a43f13
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom eq zero iff cc85a26563f0: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom eq zero iff cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom eq zero iff cc85a26563f0 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds fr Hom eq zero iff cc85a26563f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L136-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L136-L137

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_eq_zero_iff_cc85a26563f0 {f : MRing ι} : frHom P f = 0 ↔ f ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«frHom_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_eq_zero_iff_cc85a26563f0
