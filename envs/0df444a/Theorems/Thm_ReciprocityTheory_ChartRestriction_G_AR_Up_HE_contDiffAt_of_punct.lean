-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_contDiffAt_of_punct
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:17.375814+00:00
-- url     : https://prove2.me/theorems/a3053158-affa-40b3-94cc-722c5463b162
-- title:
--   HE: cont Diff At of punct
-- statement:
--   The HE construction uses the cont Diff At of punct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpStatementPfE.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpStatementPfE.lean#L97-L98

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix
noncomputable section
variable {n : ℕ}
variable {U : Set (V n)}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℂ ∞ g y := by sorry
