-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_rename_469732d254e3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_rename_469732d254e3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:21.068211+00:00
-- url     : https://prove2.me/theorems/679b6c91-1d0e-404d-b0e7-607b97c4bf79
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map rename 469732d254e3: P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map rename 469732d254e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map rename 469732d254e3 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull multi Cone Map rename 469732d254e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L107-L114

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_rename_469732d254e3 (j : Fin 2) (s : MRing (T.yyIdx ι ν κ)) :
    T.multiConeMap (T.wwCoord x δ e φ a₀ a₀) (rename (T.yyEmb j) s) =
      eval₂ (Int.castRingHom _) (fun q => C (T.yyCoord x δ e φ a₀ q) * X (blk j q.1)) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«multiConeMap_rename» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_rename_469732d254e3
