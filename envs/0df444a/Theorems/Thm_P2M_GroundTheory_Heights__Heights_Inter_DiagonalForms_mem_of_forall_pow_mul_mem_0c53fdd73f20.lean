-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mem_of_forall_pow_mul_mem_0c53fdd73f20
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mem_of_forall_pow_mul_mem_0c53fdd73f20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:29.310989+00:00
-- url     : https://prove2.me/theorems/ff525d0e-492b-41fb-963b-0f114a4d5b2b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms mem of forall pow mul mem 0c53fdd73f20: P2 M Ground Theory Heights  Heights Inter Diagonal Forms mem of forall pow mul mem 0c53fdd73f20
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms mem of forall pow mul mem 0c53fdd73f20 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms mem of forall pow mul mem 0c53fdd73f20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L41-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L41-L68

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mem_of_forall_pow_mul_mem_0c53fdd73f20 (R : Subalgebra ℤ Ω) {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ R)
    (hc : ∀ l, c l ∈ R) (hsum : ∑ l, c l * f l = 1) {y : Ω} (hy : ∀ l, ∃ n : ℕ, f l ^ n * y ∈ R) :
    y ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«mem_of_forall_pow_mul_mem» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mem_of_forall_pow_mul_mem_0c53fdd73f20
