-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_smul_left
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_smul_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:07.644641+00:00
-- url     : https://prove2.me/theorems/eeb1ba05-008d-4478-a348-8ca464ea77e0
-- title:
--   Semi Deg Idx: herm Form smul left
-- statement:
--   The Semi Deg Idx construction uses the herm Form smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean#L10-L13

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h (a • u) w = S.c a * S.h u w := by sorry
