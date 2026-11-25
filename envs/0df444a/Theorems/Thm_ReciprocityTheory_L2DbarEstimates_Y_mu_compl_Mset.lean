-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_mu_compl_Mset
-- name    : ReciprocityTheory.L2DbarEstimates.Y.mu_compl_Mset
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:01:09.103365+00:00
-- url     : https://prove2.me/theorems/e1f3a066-6630-450d-b9fe-4751d9ab5b12
-- title:
--   Y: mu compl Mset
-- statement:
--   The Y construction uses the mu compl Mset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNull.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNull.lean#L16-L18

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
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

theorem ReciprocityTheory.L2DbarEstimates.Y.mu_compl_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hN : EXTNullStatement n) (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) : A.mu (A.Mset w0 s De)ᶜ = 0 := by sorry
