-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_valAt_eq_31bc992f98c6
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_valAt_eq_31bc992f98c6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:23.916+00:00
-- url     : https://prove2.me/theorems/3f44b832-bdff-4a0e-8db6-51441e7647dd
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free val At eq 31bc992f98c6: P2 M Ground Theory Heights  Heights Lower Bound Free val At eq 31bc992f98c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free val At eq 31bc992f98c6 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free val At eq 31bc992f98c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L56-L61

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_valAt_eq_31bc992f98c6 {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v : ℂ} (hv : IsValueAt y s z v) : valAt y s z = v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«valAt_eq» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_valAt_eq_31bc992f98c6
