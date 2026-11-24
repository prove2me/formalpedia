-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_mul_d91c22cfe178
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_mul_d91c22cfe178
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:37.414366+00:00
-- url     : https://prove2.me/theorems/b38eec0a-b15d-40d7-bc74-ba4f4394400a
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Value At mul d91c22cfe178: P2 M Ground Theory Heights  Heights Lower Bound Free is Value At mul d91c22cfe178
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Value At mul d91c22cfe178 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Value At mul d91c22cfe178 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L41-L49

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_mul_d91c22cfe178 {y : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt y s z v) (hw : IsValueAt y t z w) : IsValueAt y (s * t) z (v * w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isValueAt_mul» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_mul_d91c22cfe178
