-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_log_norm_sub_le
-- name    : ReciprocityTheory.Cheb.abs_log_norm_sub_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:58.19079+00:00
-- url     : https://prove2.me/theorems/a90273d9-2224-4203-ba0a-0c70053323a8
-- title:
--   Cheb: abs log norm sub le
-- statement:
--   The Cheb construction uses the abs log norm sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L114-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L114-L129

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

theorem ReciprocityTheory.Cheb.abs_log_norm_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    |Real.log (mixedEmbedding.norm (y + k)) - Real.log (mixedEmbedding.norm y)| ≤
      (Module.finrank ℚ E : ℝ) * (2 * B / a) := by sorry
