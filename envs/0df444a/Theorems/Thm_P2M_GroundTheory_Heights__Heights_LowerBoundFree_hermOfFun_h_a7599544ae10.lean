-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_hermOfFun_h_a7599544ae10
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_hermOfFun_h_a7599544ae10
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:20.486673+00:00
-- url     : https://prove2.me/theorems/03989bcf-2bcc-4fc1-8a2e-ab20ab644253
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free herm Of Fun h a7599544ae10: P2 M Ground Theory Heights  Heights Lower Bound Free herm Of Fun h a7599544ae10
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free herm Of Fun h a7599544ae10 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free herm Of Fun h a7599544ae10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L151-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L151-L171

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_hermOfFun_h_a7599544ae10 {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} (hF : IsHomogOfDeg a F)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hpos : 0 < F z) :
    (hermOfFun ι a F).h z = F z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«hermOfFun_h» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_hermOfFun_h_a7599544ae10
