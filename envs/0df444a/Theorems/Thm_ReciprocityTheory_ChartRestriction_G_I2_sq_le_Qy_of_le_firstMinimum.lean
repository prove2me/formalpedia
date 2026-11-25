-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sq_le_Qy_of_le_firstMinimum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sq_le_Qy_of_le_firstMinimum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:01.679827+00:00
-- url     : https://prove2.me/theorems/e1e377e5-49f6-4287-bf44-99c1a000ae5a
-- title:
--   I2: sq le Qy of le first Minimum
-- statement:
--   The I2 construction uses the sq le Qy of le first Minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitC.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitC.lean#L12-L16

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

theorem ReciprocityTheory.ChartRestriction.G.I2.sq_le_Qy_of_le_firstMinimum (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (hne : x ≠ 0) : X.la1 ≤ ‖x‖ := by sorry
