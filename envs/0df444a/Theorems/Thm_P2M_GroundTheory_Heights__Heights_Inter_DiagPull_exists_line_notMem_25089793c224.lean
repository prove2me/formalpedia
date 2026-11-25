-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_notMem_25089793c224
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_notMem_25089793c224
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:31.470184+00:00
-- url     : https://prove2.me/theorems/4bbba542-7bde-4284-8a4d-f33e0e30d66b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull exists line not Mem 25089793c224: P2 M Ground Theory Heights  Heights Inter Diag Pull exists line not Mem 25089793c224
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull exists line not Mem 25089793c224 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull exists line not Mem 25089793c224 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L143-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L143-L159

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_notMem_25089793c224 {W : Ideal (MRing (T.wwIdx ι ν κ))} (hW : W.IsPrime)
    (hΔ : T.wwIdeal x δ e φ a₀ a₀ ≤ W) (hrel : IsRelevant W) :
    ∃ k : κ, (X ⟨.line0, k⟩ : MRing (T.wwIdx ι ν κ)) ∉ W ∧ (X ⟨.line1, k⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«exists_line_notMem» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_notMem_25089793c224
