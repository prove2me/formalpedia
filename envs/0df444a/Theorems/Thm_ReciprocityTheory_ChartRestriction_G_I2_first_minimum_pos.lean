-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_first_minimum_pos
-- name    : ReciprocityTheory.ChartRestriction.G.I2.first_minimum_pos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:25.387658+00:00
-- url     : https://prove2.me/theorems/5355916c-fdc3-4972-bc06-8139089c4ce7
-- title:
--   I2: first minimum pos
-- statement:
--   The I2 construction uses the first minimum pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitC.lean#L25-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitC.lean#L25-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.first_minimum_pos (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) : 0 < X.la1 := by sorry
