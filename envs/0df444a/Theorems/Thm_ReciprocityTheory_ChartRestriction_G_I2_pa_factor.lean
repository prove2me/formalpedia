-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_factor
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_factor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:32.938883+00:00
-- url     : https://prove2.me/theorems/72065673-4534-4339-94e5-4aed2c4b29a8
-- title:
--   I2: pa factor
-- statement:
--   The I2 construction uses the pa factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L252-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L252-L272

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_factor (q : ℕ) (v g g' : EuclideanSpace ℂ ι) (kk : ℤ) (hkk : (Hf g' g).im = kk) :
    cexp (-(Real.pi * q * (Hf g g').im) * I) *
      cexp (q * Real.pi * Hf (v + g') (g + g') - q * Real.pi * Hf (g + g') (g + g') / 2) =
    cexp (q * Real.pi * Hf v g' + q * Real.pi * Hf g' g' / 2) *
      cexp (q * Real.pi * Hf v g - q * Real.pi * Hf g g / 2) := by sorry
