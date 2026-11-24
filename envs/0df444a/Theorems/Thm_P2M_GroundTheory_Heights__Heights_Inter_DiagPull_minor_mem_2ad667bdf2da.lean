-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_minor_mem_2ad667bdf2da
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_minor_mem_2ad667bdf2da
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:58.288962+00:00
-- url     : https://prove2.me/theorems/c6b7bf23-d361-48ea-98b6-d851e4c8358c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull minor mem 2ad667bdf2da: P2 M Ground Theory Heights  Heights Inter Diag Pull minor mem 2ad667bdf2da
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull minor mem 2ad667bdf2da construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull minor mem 2ad667bdf2da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L124-L129

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_minor_mem_2ad667bdf2da (i k : κ) :
    (X ⟨.line0, i⟩ * X ⟨.line1, k⟩ - X ⟨.line0, k⟩ * X ⟨.line1, i⟩ : MRing (T.wwIdx ι ν κ)) ∈
      T.wwIdeal x δ e φ a₀ a₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«minor_mem» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_minor_mem_2ad667bdf2da
