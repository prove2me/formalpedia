-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_Hf_im
-- name    : ReciprocityTheory.ChartRestriction.G.I2.lemS_Hf_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:41.574169+00:00
-- url     : https://prove2.me/theorems/8770044f-5179-4a34-8a2e-025718bd15b4
-- title:
--   I2: lem S Hf im
-- statement:
--   The I2 construction uses the lem S Hf im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L12-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.lemS_Hf_im (x y : EuclideanSpace ℂ ι) :
    (Hf x y).im = inner ℝ y ((-I : ℂ) • x) := by sorry
