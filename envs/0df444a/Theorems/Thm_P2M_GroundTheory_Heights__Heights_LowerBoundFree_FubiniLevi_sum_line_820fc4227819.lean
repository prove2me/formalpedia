-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sum_line_820fc4227819
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sum_line_820fc4227819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:13.32957+00:00
-- url     : https://prove2.me/theorems/403a9223-5ad3-45ee-ad0f-e7f4aa50dcc9
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi sum line 820fc4227819: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi sum line 820fc4227819
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi sum line 820fc4227819 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi sum line 820fc4227819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L109-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sum_line_820fc4227819 (f : (Σ _ : Unit, Fin 2) → ℝ) : ∑ p, f p = f ⟨(), 0⟩ + f ⟨(), 1⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«sum_line» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sum_line_820fc4227819
