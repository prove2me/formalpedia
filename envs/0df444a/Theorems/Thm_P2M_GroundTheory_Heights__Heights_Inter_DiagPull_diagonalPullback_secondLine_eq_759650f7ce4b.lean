-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_diagonalPullback_secondLine_eq_759650f7ce4b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_diagonalPullback_secondLine_eq_759650f7ce4b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:19.212963+00:00
-- url     : https://prove2.me/theorems/d2f6ef62-e2d2-490d-acb5-f0aa781c70c6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull diagonal Pullback second Line eq 759650f7ce4b: P2 M Ground Theory Heights  Heights Inter Diag Pull diagonal Pullback second Line eq 759650f7ce4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull diagonal Pullback second Line eq 759650f7ce4b construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull diagonal Pullback second Line eq 759650f7ce4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L218-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L218-L225

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
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
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
omit [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_diagonalPullback_secondLine_eq_759650f7ce4b {z : (Σ k, T.wwIdx ι ν κ k) → ℂ} {c : ℂ} (hk : ∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩) :
    (fun p => z (T.yyEmb 1 p)) = fun p => lineScal c p.1 * z (T.yyEmb 0 p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«diagonalPullback_secondLine_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_diagonalPullback_secondLine_eq_759650f7ce4b
