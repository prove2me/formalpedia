-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_rsgn_add
-- name    : ReciprocityTheory.Cheb.rsgn_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:03.789591+00:00
-- url     : https://prove2.me/theorems/eeeb5374-5269-586a-bf7b-4e7b94c09c4a
-- title:
--   Cheb: rsgn add
-- statement:
--   The Cheb construction uses the rsgn add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L168-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L168-L182

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

theorem ReciprocityTheory.Cheb.rsgn_add (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y) :
    rsgn (y + k) = rsgn y := by sorry
