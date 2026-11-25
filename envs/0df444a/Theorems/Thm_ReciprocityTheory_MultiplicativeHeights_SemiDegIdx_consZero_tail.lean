-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_tail
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_tail
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:58.3158+00:00
-- url     : https://prove2.me/theorems/153ee403-ca33-4363-a152-6bb0fb46ccfb
-- title:
--   Semi Deg Idx: cons Zero tail
-- statement:
--   The Semi Deg Idx construction uses the cons Zero tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCB.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCB.lean#L30-L35

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField
open scoped nonZeroDivisors

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_tail (K : Type) [Field K] {k : ℕ} (x : Fin (k + 1) → K) (hx : x 0 = 0) :
    consZero K k (Fin.tail x) = x := by sorry
