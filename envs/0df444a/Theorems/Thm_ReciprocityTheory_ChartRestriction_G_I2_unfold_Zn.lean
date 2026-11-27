-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_unfold_Zn
-- name    : ReciprocityTheory.ChartRestriction.G.I2.unfold_Zn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:52.780281+00:00
-- url     : https://prove2.me/theorems/42dcf420-488f-4b24-a8a0-e656daf56df7
-- title:
--   I2: unfold Zn
-- statement:
--   The I2 construction uses the unfold Zn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/UnfoldZn.lean#L9-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/UnfoldZn.lean#L9-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_UnfoldZn
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

theorem ReciprocityTheory.ChartRestriction.G.I2.unfold_Zn {d : ℕ} (g : (Fin d → ℝ) → ENNReal) :
    ∫⁻ x, g x = ∑' n : Fin d → ℤ, ∫⁻ x in cubeIco (Fin d), g (x + fun i => (n i : ℝ)) := by sorry
