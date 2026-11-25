-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_mem_intVec
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_mem_intVec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:53.659341+00:00
-- url     : https://prove2.me/theorems/9ed7fb90-2800-4745-8701-bb86328eb321
-- title:
--   Semi Deg Idx: cons Zero mem int Vec
-- statement:
--   The Semi Deg Idx construction uses the cons Zero mem int Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCB.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCB.lean#L47-L56

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} {y : Fin k → K} :
    consZero K k y ∈ intVec K (k + 1) ↔ y ∈ intVec K k := by sorry
