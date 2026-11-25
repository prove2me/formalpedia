-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_unique_d279c6dbe068
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_unique_d279c6dbe068
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:29.829698+00:00
-- url     : https://prove2.me/theorems/c315f5b4-7239-42e6-bc1c-45a8f23bcaba
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Value At unique d279c6dbe068: P2 M Ground Theory Heights  Heights Lower Bound Free is Value At unique d279c6dbe068
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Value At unique d279c6dbe068 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Value At unique d279c6dbe068 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L25-L39

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
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_unique_d279c6dbe068 {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v w : ℂ} (hv : IsValueAt y s z v) (hw : IsValueAt y s z w) :
    v = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isValueAt_unique» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_unique_d279c6dbe068
