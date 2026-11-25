-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_log_sub_log_le_of_half
-- name    : ReciprocityTheory.Cheb.abs_log_sub_log_le_of_half
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:31.805617+00:00
-- url     : https://prove2.me/theorems/b3190675-2bff-4838-86d3-5527f32f77a6
-- title:
--   Cheb: abs log sub log le of half
-- statement:
--   The Cheb construction uses the abs log sub log le of half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L10-L28

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

theorem ReciprocityTheory.Cheb.abs_log_sub_log_le_of_half {a b δ : ℝ} (hb : 0 < b) (hab : |a - b| ≤ δ) (ha : b / 2 ≤ a) :
    |Real.log a - Real.log b| ≤ 2 * δ / b := by sorry
