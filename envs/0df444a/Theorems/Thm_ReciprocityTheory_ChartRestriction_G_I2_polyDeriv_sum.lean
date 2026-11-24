-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:44.610128+00:00
-- url     : https://prove2.me/theorems/1e221c62-622a-49d8-8ae7-cb1b3a57434e
-- title:
--   I2: poly Deriv sum
-- statement:
--   The I2 construction uses the poly Deriv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L23-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory

theorem ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_sum {σ W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (s : Finset ι) (c : ι → ℂ) (F : ι → W → ℂ)
    (hF : ∀ i ∈ s, ∀ k : ℕ, ContDiff ℂ k (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x := by sorry
