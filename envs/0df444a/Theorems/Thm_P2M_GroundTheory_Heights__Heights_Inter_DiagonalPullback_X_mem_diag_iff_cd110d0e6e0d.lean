-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_X_mem_diag_iff_cd110d0e6e0d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_X_mem_diag_iff_cd110d0e6e0d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:42.276633+00:00
-- url     : https://prove2.me/theorems/8ea0d911-b0be-4e5a-ba60-51bb14b436c5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Pullback X mem diag iff cd110d0e6e0d: P2 M Ground Theory Heights  Heights Inter Diagonal Pullback X mem diag iff cd110d0e6e0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Pullback X mem diag iff cd110d0e6e0d construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Pullback X mem diag iff cd110d0e6e0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L50-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_X_mem_diag_iff_cd110d0e6e0d {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
    (p : Σ k, T.wwIdx ι ν κ k) :
    (X p : MRing (T.wwIdx ι ν κ)) ∈ T.wwIdeal x δ e φ a₀ a₀ ↔ T.wwCoord x δ e φ a₀ a₀ p = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalPullback».«X_mem_diag_iff» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_X_mem_diag_iff_cd110d0e6e0d
