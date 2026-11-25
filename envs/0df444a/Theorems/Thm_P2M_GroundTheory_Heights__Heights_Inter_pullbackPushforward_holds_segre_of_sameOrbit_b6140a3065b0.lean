-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_segre_of_sameOrbit_b6140a3065b0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_segre_of_sameOrbit_b6140a3065b0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:39.153353+00:00
-- url     : https://prove2.me/theorems/5897b9ce-f294-58df-9bf6-da4a4fbf8fe1
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds segre of same Orbit b6140a3065b0: P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds segre of same Orbit b6140a30
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds segre of same Orbit b6140a3065b0 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds segre of same Orbit b6140a3065b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L32-L35

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

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_segre_of_sameOrbit_b6140a3065b0 {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ μ : ℂ, μ ≠ 0 ∧ segre z = μ • segre z' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackPushforward_holds».«segre_of_sameOrbit» := P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_segre_of_sameOrbit_b6140a3065b0
