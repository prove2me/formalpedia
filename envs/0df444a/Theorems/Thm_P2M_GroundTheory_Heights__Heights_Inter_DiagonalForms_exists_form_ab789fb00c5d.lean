-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_form_ab789fb00c5d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_form_ab789fb00c5d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:31.331442+00:00
-- url     : https://prove2.me/theorems/14810a66-8319-40e6-92e2-523ff42932ff
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists form ab789fb00c5d: P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists form ab789fb00c5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists form ab789fb00c5d construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists form ab789fb00c5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L308-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L308-L353

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
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_form_ab789fb00c5d (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) {r : Ω} (hr : r ∈ chartRing ℤ x i) :
    ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧
      aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«exists_form» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_form_ab789fb00c5d
