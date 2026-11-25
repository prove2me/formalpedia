-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_wwCoord_eq_51b851e8e365
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_wwCoord_eq_51b851e8e365
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:22.404977+00:00
-- url     : https://prove2.me/theorems/efd734bf-8be0-5f62-a88b-90b6d29c8f1a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor ww Coord eq 51b851e8e365: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor ww Coord eq 51b851e8e365
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor ww Coord eq 51b851e8e365 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor ww Coord eq 51b851e8e365 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L157-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L157-L184

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_wwCoord_eq_51b851e8e365 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (F : Subfield Ω)
    (i : ι) (l₀ : ν) (k₀ k₁ : κ) (hx : x i ≠ 0) (hδ : δ l₀ ≠ 0) (xb : ι → F) (ε : ν → F) (c₀ c₁ : κ → F)
    (hxb : ∀ j, (xb j : Ω) = x j / x i) (hε : ∀ l, (ε l : Ω) = δ l / δ l₀)
    (hc : ∀ k, φ k = (c₀ k : Ω) • φ k₀ + (c₁ k : Ω) • φ k₁) (b₀ b₁ : Φ) (w : Fin 2 → Φ)
    (h₀ : T.lineVal e (φ k₀) b₀ ≠ 0) (h₁ : T.lineVal e (φ k₀) b₁ ≠ 0)
    (hw₀ : w 0 = T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀)
    (hw₁ : w 1 = T.lineVal e (φ k₁) b₁ / T.lineVal e (φ k₀) b₁) :
    T.wwCoord x δ e φ b₀ b₁ = fun p => blockScale (algebraMap Ω Φ (x i)) (algebraMap Ω Φ (δ l₀))
      (T.lineVal e (φ k₀) b₀) (T.lineVal e (φ k₀) b₁) p.1 *
        eval₂ ((algebraMap Ω Φ).comp F.subtype) w (ratioPoly xb ε c₀ c₁ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«wwCoord_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_wwCoord_eq_51b851e8e365
