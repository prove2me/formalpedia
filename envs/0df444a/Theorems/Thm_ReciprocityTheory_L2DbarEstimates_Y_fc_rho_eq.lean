-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_rho_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fc_rho_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:49.495039+00:00
-- url     : https://prove2.me/theorems/b3446a6d-42d2-55c9-be1f-30f08f5cc66a
-- title:
--   Y: fc rho eq
-- statement:
--   The Y construction uses the fc rho eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcC.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcC.lean#L20-L30

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
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
open scoped ContDiff ENNReal
noncomputable section
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.fc_rho_eq {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) :
    Real.exp (A.ph A.kap (A.pick y) y) /
        ‖(fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det‖ ^ 2 =
      Real.exp (A.ph A.kap i y) / ‖(fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det‖ ^ 2 := by sorry
