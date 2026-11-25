-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_sameOrbit_comp_b367633ae983
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_sameOrbit_comp_b367633ae983
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:10.707586+00:00
-- url     : https://prove2.me/theorems/9cba0a5a-13ac-5cf6-9d19-38ec6cfe57fc
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds same Orbit comp b367633ae983: P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds same Orbit comp b367633ae983
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds same Orbit comp b367633ae983 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds same Orbit comp b367633ae983 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L39-L46

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
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_sameOrbit_comp_b367633ae983 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {z z' : (Σ k', ι' k') → ℂ} (h : SameOrbit z z') :
    SameOrbit (fun p => z (v p)) (fun p => z' (v p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackPushforward_holds».«sameOrbit_comp» := P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_sameOrbit_comp_b367633ae983
