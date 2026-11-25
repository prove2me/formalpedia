-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_im_eq_zero_of_lt
-- name    : ReciprocityTheory.ChartRestriction.G.I2.im_eq_zero_of_lt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:09.407668+00:00
-- url     : https://prove2.me/theorems/32176f5f-303d-529e-9359-35fae3b808ef
-- title:
--   I2: im eq zero of lt
-- statement:
--   The I2 construction uses the im eq zero of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitB.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitB.lean#L108-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitB
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

theorem ReciprocityTheory.ChartRestriction.G.I2.im_eq_zero_of_lt (X : PT E) {x y : Vsp X.dim} (hx : x ∈ X.L) (hy : y ∈ X.L)
    (h : |(Hf x y).im| < 1) : (Hf x y).im = 0 := by sorry
