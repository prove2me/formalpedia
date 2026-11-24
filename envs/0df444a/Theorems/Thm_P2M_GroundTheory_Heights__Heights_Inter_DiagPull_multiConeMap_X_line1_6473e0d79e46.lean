-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line1_6473e0d79e46
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line1_6473e0d79e46
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:13.21683+00:00
-- url     : https://prove2.me/theorems/30c1dd58-eed2-4d0b-b1ef-47e986a247fe
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line1 6473e0d79e46: P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line1 6473e0d79e46
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line1 6473e0d79e46 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line1 6473e0d79e46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L120-L122

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line1_6473e0d79e46 (k : κ) :
    T.multiConeMap (T.wwCoord x δ e φ a₀ a₀) (X ⟨.line1, k⟩) = C (T.lineVal e (φ k) a₀) * X .line1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«multiConeMap_X_line1» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line1_6473e0d79e46
