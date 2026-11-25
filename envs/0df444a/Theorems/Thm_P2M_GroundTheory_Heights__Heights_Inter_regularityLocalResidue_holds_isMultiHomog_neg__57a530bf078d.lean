-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_neg__57a530bf078d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_neg__57a530bf078d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:46.091679+00:00
-- url     : https://prove2.me/theorems/e1b85116-007f-5719-b211-639cb45c4b0f
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog neg  57a530bf078d: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog neg
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog neg  57a530bf078d construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds is Multi Homog neg  57a530bf078d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L29-L33

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_neg__57a530bf078d {R : Type*} [CommRing R] {f : MRingOver R ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«isMultiHomog_neg'» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_neg__57a530bf078d
