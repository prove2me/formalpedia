-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_curveRing_of_forall_780a7c40c442
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_curveRing_of_forall_780a7c40c442
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:24.690065+00:00
-- url     : https://prove2.me/theorems/f6271e52-9b99-5063-8d48-d3b65d766c94
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem curve Ring of forall 780a7c40c442: P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem curve Ring of forall 780a7c40c442
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem curve Ring of forall 780a7c40c442 construction uses the P2 M Ground Theory Heights  Heights Closed Point Affine Chart mem curve Ring of forall 780a7c40c442 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L29-L35

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_curveRing_of_forall_780a7c40c442 {b : K'}
    (h : ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t)) : b ∈ curveRing y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointAffineChart».«mem_curveRing_of_forall» := P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_curveRing_of_forall_780a7c40c442
