-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_logMap_sub_le
-- name    : ReciprocityTheory.Cheb.abs_logMap_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:22.671003+00:00
-- url     : https://prove2.me/theorems/32732c76-80df-4c41-b98f-0b33a0ae9650
-- title:
--   Cheb: abs log Map sub le
-- statement:
--   The Cheb construction uses the abs log Map sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L131-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L131-L159

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
variable {y k : mixedSpace E} {B a : ℝ}

theorem ReciprocityTheory.Cheb.abs_logMap_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) (w : {w : InfinitePlace E // w ≠ w₀}) :
    |logMap (y + k) w - logMap y w| ≤ 4 * (2 * B / a) := by sorry
