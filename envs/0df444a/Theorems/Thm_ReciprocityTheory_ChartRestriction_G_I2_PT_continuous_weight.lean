-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_continuous_weight
-- name    : ReciprocityTheory.ChartRestriction.G.I2.PT.continuous_weight
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:51.743096+00:00
-- url     : https://prove2.me/theorems/b08c6a03-1291-49e4-86e5-9380525a2c21
-- title:
--   PT: continuous weight
-- statement:
--   The PT construction uses the continuous weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L62-L71

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
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.PT.continuous_weight (q n : ℕ) :
    Continuous fun v : Fin n → Vsp X.dim => (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) := by sorry
