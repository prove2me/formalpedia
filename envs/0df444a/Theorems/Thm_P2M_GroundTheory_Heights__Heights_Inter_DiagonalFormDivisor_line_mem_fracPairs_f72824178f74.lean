-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_line_mem_fracPairs_f72824178f74
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_line_mem_fracPairs_f72824178f74
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:39.522216+00:00
-- url     : https://prove2.me/theorems/406a7593-8343-4fb8-828f-5d846f1a441b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line mem frac Pairs f72824178f74: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line mem frac Pairs f72824178f74
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line mem frac Pairs f72824178f74 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line mem frac Pairs f72824178f74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L204-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L204-L229

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_line_mem_fracPairs_f72824178f74 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (k₀ k₁ : κ)
    (b₀ b₁ : Φ) (h₀ : T.lineVal e (φ k₀) b₀ ≠ 0) (h₁ : T.lineVal e (φ k₀) b₁ ≠ 0) :
    (T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀, T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀) ∈
        fracPairs (T.wwCoord x δ e φ b₀ b₁) (T.wwCoord x δ e φ b₀ b₀) ∧
      (T.lineVal e (φ k₁) b₁ / T.lineVal e (φ k₀) b₁, T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀) ∈
        fracPairs (T.wwCoord x δ e φ b₀ b₁) (T.wwCoord x δ e φ b₀ b₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«line_mem_fracPairs» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_line_mem_fracPairs_f72824178f74
