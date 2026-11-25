-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isNilpotent_of_trace_pow
-- name    : ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:16:54.957905+00:00
-- url     : https://prove2.me/theorems/00c04ecd-417b-4213-b5e9-9fc67cfa25be
-- title:
--   Y: is Nilpotent of trace pow
-- statement:
--   The Y construction uses the is Nilpotent of trace pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/UniNilp.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/UniNilp.lean#L75-L78

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TracePowEqZeroOfLeDim
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
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
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow {K : Type*} [Field K] [CharZero K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    IsNilpotent N := by sorry
