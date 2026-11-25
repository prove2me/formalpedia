-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_prop_543201ba58eb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_prop_543201ba58eb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:39.46883+00:00
-- url     : https://prove2.me/theorems/2dcf7c0c-5108-4801-b5d4-8e364cc712cb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull exists line prop 543201ba58eb: P2 M Ground Theory Heights  Heights Inter Diag Pull exists line prop 543201ba58eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull exists line prop 543201ba58eb construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull exists line prop 543201ba58eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L200-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L200-L215

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_prop_543201ba58eb {z : (Σ k, T.wwIdx ι ν κ k) → ℂ} (hz : z ∈ mcPts (T.wwIdeal x δ e φ a₀ a₀)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«exists_line_prop» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_prop_543201ba58eb
