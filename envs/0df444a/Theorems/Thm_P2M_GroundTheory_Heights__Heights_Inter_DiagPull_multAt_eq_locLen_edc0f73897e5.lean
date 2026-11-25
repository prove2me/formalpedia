-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multAt_eq_locLen_edc0f73897e5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multAt_eq_locLen_edc0f73897e5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:25.492813+00:00
-- url     : https://prove2.me/theorems/36914448-bde8-4f3d-90ee-f87ae9d7c34e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull mult At eq loc Len edc0f73897e5: P2 M Ground Theory Heights  Heights Inter Diag Pull mult At eq loc Len edc0f73897e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull mult At eq loc Len edc0f73897e5 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull mult At eq loc Len edc0f73897e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L162-L164

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multAt_eq_locLen_edc0f73897e5 (J W : Ideal (MRing (T.wwIdx ι ν κ))) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing (T.wwIdx ι ν κ) ⧸ J) ⟨W, hW⟩).toNat := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«multAt_eq_locLen» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multAt_eq_locLen_edc0f73897e5
