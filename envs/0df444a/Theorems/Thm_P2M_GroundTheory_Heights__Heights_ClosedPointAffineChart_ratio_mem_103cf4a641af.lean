-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_ratio_mem_103cf4a641af
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_ratio_mem_103cf4a641af
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:43.367246+00:00
-- url     : https://prove2.me/theorems/d5b42ebe-6e29-5841-9649-bf2dfa233873
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Affine Chart ratio mem 103cf4a641af: P2 M Ground Theory Heights  Heights Closed Point Affine Chart ratio mem 103cf4a641af
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Affine Chart ratio mem 103cf4a641af construction uses the P2 M Ground Theory Heights  Heights Closed Point Affine Chart ratio mem 103cf4a641af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointChart.lean#L18-L19

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_ratio_mem_103cf4a641af (t u : T) : y ⟨(), u⟩ / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointAffineChart».«ratio_mem» := P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_ratio_mem_103cf4a641af
