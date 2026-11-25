-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_rpow_neg_sub_le
-- name    : ReciprocityTheory.Cheb.abs_rpow_neg_sub_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:48.895602+00:00
-- url     : https://prove2.me/theorems/85867df7-0835-4a82-a32f-07013ef065cd
-- title:
--   Cheb: abs rpow neg sub le
-- statement:
--   The Cheb construction uses the abs rpow neg sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L211-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L211-L218

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

theorem ReciprocityTheory.Cheb.abs_rpow_neg_sub_le {s m N N' : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) (hN' : m ≤ N') :
    |N' ^ (-s) - N ^ (-s)| ≤ s * |Real.log N' - Real.log N| * m⁻¹ := by sorry
