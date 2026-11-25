-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_loc
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fn_loc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:51:53.748471+00:00
-- url     : https://prove2.me/theorems/f29b3800-a76b-46e8-9c34-784506458dc7
-- title:
--   Y: fn loc
-- statement:
--   The Y construction uses the fn loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullB.lean#L132-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullB.lean#L132-L250

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.fn_loc (hD : A.D0 L w w0 s) {la : La} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤)
    (i : ι) {v : V n} (hv : v ∈ (A.chart i).target) :
    ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) < ⊤ := by sorry
