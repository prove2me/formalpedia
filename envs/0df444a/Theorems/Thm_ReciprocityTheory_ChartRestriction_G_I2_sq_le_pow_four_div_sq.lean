-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sq_le_pow_four_div_sq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sq_le_pow_four_div_sq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:11.572116+00:00
-- url     : https://prove2.me/theorems/c6b9f47a-6341-574a-829e-ecbe4f465bc4
-- title:
--   I2: sq le pow four div sq
-- statement:
--   The I2 construction uses the sq le pow four div sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitG.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitG.lean#L95-L107

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitG
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.sq_le_pow_four_div_sq {d N la u : ℝ} (hd : 2 ≤ d) (hN : N ≤ d) (hla : 0 < la) (hu0 : 0 ≤ u)
    (hu : u ≤ N / la + 1 / la) : u ^ 2 ≤ d ^ 4 / la ^ 2 := by sorry
