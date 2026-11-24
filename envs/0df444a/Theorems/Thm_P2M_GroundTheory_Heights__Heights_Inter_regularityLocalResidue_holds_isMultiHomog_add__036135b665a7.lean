-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:08.936361+00:00
-- url     : https://prove2.me/theorems/c9f6a09e-b2ff-4d50-b710-07e1f4dcbadb
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog add  036135b665a7: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog add
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog add  036135b665a7 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog add  036135b665a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L21-L27

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7 {R : Type*} [CommRing R] {f g : MRingOver R ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«isMultiHomog_add'» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7
