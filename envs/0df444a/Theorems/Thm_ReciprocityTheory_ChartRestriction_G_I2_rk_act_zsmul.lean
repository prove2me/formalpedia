-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rk_act_zsmul
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rk_act_zsmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:04.172154+00:00
-- url     : https://prove2.me/theorems/40bab52d-4949-52af-8180-b72cfbee9e20
-- title:
--   I2: rk act zsmul
-- statement:
--   The I2 construction uses the rk act zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L27-L29

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

theorem ReciprocityTheory.ChartRestriction.G.I2.rk_act_zsmul (α : 𝓞 E) (n : ℤ) (v : Vsp dim) : act α (n • v) = n • act α v := by sorry
