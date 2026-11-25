-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rk_act_natCast
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rk_act_natCast
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:27.425196+00:00
-- url     : https://prove2.me/theorems/7a1b6aff-3250-409e-a8d2-ad748190ceb7
-- title:
--   I2: rk act nat Cast
-- statement:
--   The I2 construction uses the rk act nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L23-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
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
variable {dim : (E →+* ℂ) → ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.rk_act_natCast (n : ℕ) (v : Vsp dim) : act (n : 𝓞 E) v = (n : ℤ) • v := by sorry
