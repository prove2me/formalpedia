-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_chart_of_mem_curveRing_93a3946b1876
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_chart_of_mem_curveRing_93a3946b1876
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:39.552875+00:00
-- url     : https://prove2.me/theorems/ce01bd97-830f-487c-8798-09aeb30aeec2
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem chart of mem curve Ring 93a3946b1876: P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem chart of mem curve Ring 93a394
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem chart of mem curve Ring 93a3946b1876 construction uses the P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem chart of mem curve Ring 93a3946b1876 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointAffineChart
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_chart_of_mem_curveRing_93a3946b1876 {b : K'} (hb : b ∈ curveRing y) (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    b ∈ chartRingZ y (fun _ => t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointAffineChart».«mem_chart_of_mem_curveRing» := P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_chart_of_mem_curveRing_93a3946b1876
