-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_norm_logMap_sub_le
-- name    : ReciprocityTheory.Cheb.norm_logMap_sub_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:10.813244+00:00
-- url     : https://prove2.me/theorems/485fd52e-4489-4df7-926d-486777ab19d8
-- title:
--   Cheb: norm log Map sub le
-- statement:
--   The Cheb construction uses the norm log Map sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L161-L166

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

theorem ReciprocityTheory.Cheb.norm_logMap_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) : ‖logMap (y + k) - logMap y‖ ≤ 4 * (2 * B / a) := by sorry
