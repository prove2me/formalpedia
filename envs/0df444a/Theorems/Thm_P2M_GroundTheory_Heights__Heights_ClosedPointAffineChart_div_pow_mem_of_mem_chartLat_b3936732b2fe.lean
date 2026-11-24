-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_div_pow_mem_of_mem_chartLat_b3936732b2fe
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_div_pow_mem_of_mem_chartLat_b3936732b2fe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:43.231898+00:00
-- url     : https://prove2.me/theorems/5a3204b7-161b-4058-b997-61145a05531c
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Affine Chart div pow mem of mem chart Lat b3936732b2fe: P2 M Ground Theory Heights  Heights Closed Point Affine Chart div pow mem of mem chart Lat b393
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Affine Chart div pow mem of mem chart Lat b3936732b2fe construction uses the P2 M Ground Theory Heights  Heights Closed Point Affine Chart div pow mem of mem chart Lat b3936732b2fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L39-L43

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_div_pow_mem_of_mem_chartLat_b3936732b2fe {e : ℕ} {g : K'} (hg : g ∈ chartLat y 1 e) (t : T)
    (ht : y ⟨(), t⟩ ≠ 0) : g / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointAffineChart».«div_pow_mem_of_mem_chartLat» := P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_div_pow_mem_of_mem_chartLat_b3936732b2fe
