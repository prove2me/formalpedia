-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_eq_mulVec
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_eq_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:44.495801+00:00
-- url     : https://prove2.me/theorems/c87061b8-da7a-4477-a67e-1a913b61f599
-- title:
--   Semi Deg Idx: herm Form eq mul Vec
-- statement:
--   The Semi Deg Idx construction uses the herm Form eq mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L15-L18

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
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
open NumberField Matrix
open scoped nonZeroDivisors

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_eq_mulVec {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.h u w = ∑ b, (∑ a, S.c (u a) * S.G a b) * w b := by sorry
