-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_injective
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:37.172088+00:00
-- url     : https://prove2.me/theorems/c731eb2a-f148-4855-a82b-07c72738db73
-- title:
--   Semi Deg Idx: cons Zero injective
-- statement:
--   The Semi Deg Idx construction uses the cons Zero injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCB.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCB.lean#L25-L28

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_injective (K : Type) [Field K] (k : ℕ) : Function.Injective (consZero K k) := by sorry
