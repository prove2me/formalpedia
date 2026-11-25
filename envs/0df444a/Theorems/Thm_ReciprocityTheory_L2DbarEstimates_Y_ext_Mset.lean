-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ext_Mset
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ext_Mset
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:25.490741+00:00
-- url     : https://prove2.me/theorems/39bb430f-5fb5-5052-94dc-86455cb221da
-- title:
--   Y: ext Mset
-- statement:
--   The Y construction uses the ext Mset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNull.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNull.lean#L20-L25

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ext_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hE : EXTStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (la : La) (F : ι → Y → ℂ) (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤) :
    ∃ G : ι → Y → ℂ, A.IsSec la G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → G i y = F i y := by sorry
