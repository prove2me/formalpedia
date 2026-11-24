-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_normAtPlace_add_sub_le
-- name    : ReciprocityTheory.Cheb.abs_normAtPlace_add_sub_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:24.680808+00:00
-- url     : https://prove2.me/theorems/531b90b9-0cd4-46b8-912f-402b5bb09de7
-- title:
--   Cheb: abs norm At Place add sub le
-- statement:
--   The Cheb construction uses the abs norm At Place add sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L74-L80

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

theorem ReciprocityTheory.Cheb.abs_normAtPlace_add_sub_le (w : InfinitePlace E) (y k : mixedSpace E) :
    |normAtPlace w (y + k) - normAtPlace w y| ≤ ‖k‖ := by sorry
