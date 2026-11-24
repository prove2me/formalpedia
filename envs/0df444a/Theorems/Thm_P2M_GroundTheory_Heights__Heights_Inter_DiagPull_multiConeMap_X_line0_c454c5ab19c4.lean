-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line0_c454c5ab19c4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line0_c454c5ab19c4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:00.505405+00:00
-- url     : https://prove2.me/theorems/3fa12464-c295-49a5-9fd0-8f9ed3c86710
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line0 c454c5ab19c4: P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line0 c454c5ab19c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line0 c454c5ab19c4 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map X line0 c454c5ab19c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L116-L118

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line0_c454c5ab19c4 (k : κ) :
    T.multiConeMap (T.wwCoord x δ e φ a₀ a₀) (X ⟨.line0, k⟩) = C (T.lineVal e (φ k) a₀) * X .line0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«multiConeMap_X_line0» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line0_c454c5ab19c4
