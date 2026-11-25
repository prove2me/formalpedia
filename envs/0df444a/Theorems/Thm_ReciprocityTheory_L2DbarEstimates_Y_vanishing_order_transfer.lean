-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_vanishing_order_transfer
-- name    : ReciprocityTheory.L2DbarEstimates.Y.vanishing_order_transfer
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:47.79585+00:00
-- url     : https://prove2.me/theorems/d2cabd9b-13ab-4f5d-9272-a08cdef711ef
-- title:
--   Y: vanishing order transfer
-- statement:
--   The Y construction uses the vanishing order transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/VanishingOrderTransfer.lean#L18-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/VanishingOrderTransfer.lean#L18-L85

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_VanishingOrderTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.vanishing_order_transfer (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (hw : A.IsSec L w0) (hs : ∀ k, A.IsSec L (s k)) (hN : A.IsSec (m • L) Nsec)
    (y : Y) (hy0 : w0 (A.pick y) y ≠ 0)
    (hdet : (fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det ≠ 0)
    (hvan : A.VanishOrd Nsec y (m + 1))
    {T : Type*} [TopologicalSpace T] (j : T → Y) (hj : Continuous j)
    (e : OpenPartialHomeomorph T (V n)) (he : Set.EqOn (fun t => A.zmap w0 s (j t)) e e.source)
    (t0 : T) (ht0 : t0 ∈ e.source) (hjt0 : j t0 = y) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 (e t0),
      ‖(fun t => Nsec (A.pick (j t)) (j t) / w0 (A.pick (j t)) (j t) ^ m) (e.symm v)‖ ≤
        C * ‖v - e t0‖ ^ (m + 1) := by sorry
