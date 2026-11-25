-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_pullQ_eq_local_e5fc7ce96874
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_pullQ_eq_local_e5fc7ce96874
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:48.350512+00:00
-- url     : https://prove2.me/theorems/24789f9e-b67e-5d09-ad1e-7c8aec2ae176
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds pull Q eq local e5fc7ce96874: P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds pull Q eq local e5fc7ce96874
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds pull Q eq local e5fc7ce96874 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds pull Q eq local e5fc7ce96874 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DetRestrictScalarsEqZero.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DetRestrictScalarsEqZero.lean#L21-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DetRestrictScalarsEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter
open GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}
omit [Fintype K']

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_pullQ_eq_local_e5fc7ce96874 (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i =>
      Ψ (segre fun p => R.lift x z (v p)) i.succ / Ψ (segre fun p => R.lift x z (v p)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackBadImage_holds».«pullQ_eq_local» := P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_pullQ_eq_local_e5fc7ce96874
