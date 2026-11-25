-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_so_sum_sq_ge
-- name    : ReciprocityTheory.ChartRestriction.G.I2.so_sum_sq_ge
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:50.605149+00:00
-- url     : https://prove2.me/theorems/55356608-c06a-46ce-9c5f-87a4e73b8838
-- title:
--   I2: so sum sq ge
-- statement:
--   The I2 construction uses the so sum sq ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitOA.lean#L49-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitOA.lean#L49-L90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.so_sum_sq_ge [IsCMField E] (w : E) (hw0 : w ≠ 0)
    (hw : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n) :
    2 ≤ PT.rd E ^ 2 * ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := by sorry
