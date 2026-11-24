-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_pow_mul_mem_of_le_6554d47dcac9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_pow_mul_mem_of_le_6554d47dcac9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:37.808654+00:00
-- url     : https://prove2.me/theorems/10e5ca03-e9a7-4ede-aae3-e747680fabe4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms pow mul mem of le 6554d47dcac9: P2 M Ground Theory Heights  Heights Inter Diagonal Forms pow mul mem of le 6554d47dcac9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms pow mul mem of le 6554d47dcac9 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms pow mul mem of le 6554d47dcac9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L36-L39

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
variable {Ω : Type*} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_pow_mul_mem_of_le_6554d47dcac9 {R : Subalgebra ℤ Ω} {g y : Ω} (hg : g ∈ R) {n N : ℕ} (hn : n ≤ N)
    (h : g ^ n * y ∈ R) : g ^ N * y ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«pow_mul_mem_of_le» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_pow_mul_mem_of_le_6554d47dcac9
