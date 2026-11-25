-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_rpow_neg_le_inv
-- name    : ReciprocityTheory.Cheb.rpow_neg_le_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:35.71249+00:00
-- url     : https://prove2.me/theorems/1f865628-3a71-42f1-91a3-dd15294fd100
-- title:
--   Cheb: rpow neg le inv
-- statement:
--   The Cheb construction uses the rpow neg le inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L220-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L220-L223

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

theorem ReciprocityTheory.Cheb.rpow_neg_le_inv {s m N : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) : N ^ (-s) ≤ m⁻¹ := by sorry
