-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsD_denom
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsD_denom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:39:15.424351+00:00
-- url     : https://prove2.me/theorems/2646ad50-5ad3-51e4-a4a6-e9c50fc3d395
-- title:
--   Y: bs D denom
-- statement:
--   The Y construction uses the bs D denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean#L36-L45

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.bsD_denom (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (m : ℕ) :
    A.IsSecOn (mu0 + m • L) (A.Mset w0 s De) (fun i y => σ i y * w0 i y ^ m) := by sorry
