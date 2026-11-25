-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_cross_mem_0576bce22251
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_cross_mem_0576bce22251
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:28.246479+00:00
-- url     : https://prove2.me/theorems/e623398d-5afe-4378-b4d8-b05a42646eff
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull cross mem 0576bce22251: P2 M Ground Theory Heights  Heights Inter Diag Pull cross mem 0576bce22251
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull cross mem 0576bce22251 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull cross mem 0576bce22251 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L131-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L131-L141

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_cross_mem_0576bce22251 (s : MRing (T.yyIdx ι ν κ)) (d : T.YBlk → ℕ) (hs : IsMultiHomog s d) (k : κ) :
    rename (T.yyEmb 0) s * X ⟨.line1, k⟩ ^ d .line - rename (T.yyEmb 1) s * X ⟨.line0, k⟩ ^ d .line ∈
      T.wwIdeal x δ e φ a₀ a₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«cross_mem» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_cross_mem_0576bce22251
