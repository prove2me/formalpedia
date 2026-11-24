-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_log_normAtPlace_sub_le
-- name    : ReciprocityTheory.Cheb.abs_log_normAtPlace_sub_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:48.113831+00:00
-- url     : https://prove2.me/theorems/e8fb6fd6-5f22-4992-860c-e4390766cca8
-- title:
--   Cheb: abs log norm At Place sub le
-- statement:
--   The Cheb construction uses the abs log norm At Place sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L105-L112

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

theorem ReciprocityTheory.Cheb.abs_log_normAtPlace_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) (w : InfinitePlace E) :
    |Real.log (normAtPlace w (y + k)) - Real.log (normAtPlace w y)| ≤ 2 * B / a := by sorry
