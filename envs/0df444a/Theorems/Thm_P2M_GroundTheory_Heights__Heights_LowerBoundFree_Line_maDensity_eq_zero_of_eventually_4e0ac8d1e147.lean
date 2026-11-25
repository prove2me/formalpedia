-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_maDensity_eq_zero_of_eventually_4e0ac8d1e147
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_maDensity_eq_zero_of_eventually_4e0ac8d1e147
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:51.44487+00:00
-- url     : https://prove2.me/theorems/d4e506da-79a0-409a-a9f8-a48564586e6f
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line ma Density eq zero of eventually 4e0ac8d1e147: P2 M Ground Theory Heights  Heights Lower Bound Free Line ma Density eq zero of eventually 4e0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line ma Density eq zero of eventually 4e0ac8d1e147 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line ma Density eq zero of eventually 4e0ac8d1e147 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L268-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L268-L276

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_maDensity_eq_zero_of_eventually_4e0ac8d1e147 {φ : Fin 1 → (Fin 1 → ℂ) → ℝ} {y : Fin 1 → ℂ}
    (h : ∀ j, φ j =ᶠ[nhds y] fun _ => 0) : maDensity φ y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«maDensity_eq_zero_of_eventually» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_maDensity_eq_zero_of_eventually_4e0ac8d1e147
