-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullPt_sameOrbit_d61c506d0e99
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullPt_sameOrbit_d61c506d0e99
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:51.19017+00:00
-- url     : https://prove2.me/theorems/4f9af43c-1053-5ac5-b61f-6d326395100c
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds pull Pt same Orbit d61c506d0e99: P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds pull Pt same Orbit d61c506d0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds pull Pt same Orbit d61c506d0e99 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds pull Pt same Orbit d61c506d0e99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L66-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
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
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullPt_sameOrbit_d61c506d0e99 (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    SameOrbit (pullPt R v z) (fun p => R.lift x z (v p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackPushforward_holds».«pullPt_sameOrbit» := P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullPt_sameOrbit_d61c506d0e99
