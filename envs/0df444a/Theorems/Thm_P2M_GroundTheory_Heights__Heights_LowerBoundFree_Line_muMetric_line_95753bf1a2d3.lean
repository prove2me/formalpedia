-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muMetric_line_95753bf1a2d3
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muMetric_line_95753bf1a2d3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:07.860918+00:00
-- url     : https://prove2.me/theorems/10931e64-4c6d-5062-a6ea-9a58e6955a51
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Metric line 95753bf1a2d3: P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Metric line 95753bf1a2d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Metric line 95753bf1a2d3 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Metric line 95753bf1a2d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L236-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L236-L242

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
variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muMetric_line_95753bf1a2d3 {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    muMetric (lineHodge II hII) z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«muMetric_line» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muMetric_line_95753bf1a2d3
