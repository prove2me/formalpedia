-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_zero__56eb92a444c9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_zero__56eb92a444c9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:13.179441+00:00
-- url     : https://prove2.me/theorems/463e0697-37b4-44a0-b79a-5649ec1c8afa
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog zero  56eb92a444c9: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog zero  56eb92a444c9 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog zero  56eb92a444c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L35-L37

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_zero__56eb92a444c9 {R : Type*} [CommRing R] (a : K → ℕ) : IsMultiHomog (0 : MRingOver R ι) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«isMultiHomog_zero'» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_zero__56eb92a444c9
