-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:17.181276+00:00
-- url     : https://prove2.me/theorems/a6eb1ec5-4d14-44f9-aa7a-c4848bc99e16
-- title:
--   Weighted Atlas: sqn nonneg
-- statement:
--   The Weighted Atlas construction uses the sqn nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L70-L72

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_nonneg (A : WeightedAtlas n Y ι La) (la : La) {N : ℕ} (w : Fin N → ι → Y → ℂ) (y : Y) :
    0 ≤ A.sqn la w y := by sorry
