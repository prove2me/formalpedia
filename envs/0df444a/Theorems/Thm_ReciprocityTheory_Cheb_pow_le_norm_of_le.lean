-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pow_le_norm_of_le
-- name    : ReciprocityTheory.Cheb.pow_le_norm_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:15.957511+00:00
-- url     : https://prove2.me/theorems/5ef9ddab-9e29-59ce-b3f0-c3758851d139
-- title:
--   Cheb: pow le norm of le
-- statement:
--   The Cheb construction uses the pow le norm of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L225-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L225-L228

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

theorem ReciprocityTheory.Cheb.pow_le_norm_of_le {z : mixedSpace E} {b : ℝ} (hb : 0 ≤ b) (h : ∀ w, b ≤ normAtPlace w z) :
    b ^ Module.finrank ℚ E ≤ mixedEmbedding.norm z := by sorry
