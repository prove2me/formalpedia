-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Cheb_mult_le_two__43f4dc7aa0b5
-- name    : P2M_ReciprocityTheory_Cheb_mult_le_two__43f4dc7aa0b5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:48.812922+00:00
-- url     : https://prove2.me/theorems/6f85cee6-3371-4023-b580-041647876a16
-- title:
--   P2 M Reciprocity Theory Cheb mult le two  43f4dc7aa0b5: P2 M Reciprocity Theory Cheb mult le two  43f4dc7aa0b5
-- statement:
--   The P2 M Reciprocity Theory Cheb mult le two  43f4dc7aa0b5 construction uses the P2 M Reciprocity Theory Cheb mult le two  43f4dc7aa0b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L82-L83

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

theorem P2M_ReciprocityTheory_Cheb_mult_le_two__43f4dc7aa0b5 (w : InfinitePlace E) : (mult w : ℝ) ≤ 2 := by sorry

alias «ReciprocityTheory».«Cheb».«mult_le_two'» := P2M_ReciprocityTheory_Cheb_mult_le_two__43f4dc7aa0b5
