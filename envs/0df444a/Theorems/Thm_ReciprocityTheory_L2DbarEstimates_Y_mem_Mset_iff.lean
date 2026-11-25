-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_mem_Mset_iff
-- name    : ReciprocityTheory.L2DbarEstimates.Y.mem_Mset_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:26:27.005329+00:00
-- url     : https://prove2.me/theorems/22d735fc-852f-423c-8606-776675ef52f8
-- title:
--   Y: mem Mset iff
-- statement:
--   The Y construction uses the mem Mset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContinuousOnSec.lean#L183-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContinuousOnSec.lean#L183-L201

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
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

theorem ReciprocityTheory.L2DbarEstimates.Y.mem_Mset_iff {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*}
    [AddCommGroup La] {A : WeightedAtlas n Y ι La} {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (De : MvPolynomial (Fin n) ℂ)
    (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    y ∈ A.Mset w0 s De ↔
      w0 i y ≠ 0 ∧ MvPolynomial.eval (fun k => s k i y / w0 i y) De ≠ 0 := by sorry
