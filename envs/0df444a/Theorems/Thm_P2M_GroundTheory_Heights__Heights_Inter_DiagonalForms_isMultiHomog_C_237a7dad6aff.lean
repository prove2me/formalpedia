-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_C_237a7dad6aff
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_C_237a7dad6aff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:20.682589+00:00
-- url     : https://prove2.me/theorems/6c7fae4f-edc4-4516-93ee-552b11e78731
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog C 237a7dad6aff: P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog C 237a7dad6aff
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog C 237a7dad6aff construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms is Multi Homog C 237a7dad6aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L265-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L265-L272

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_C_237a7dad6aff (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«isMultiHomog_C» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_C_237a7dad6aff
