-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_sum_right
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_sum_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:46.881728+00:00
-- url     : https://prove2.me/theorems/47f2c069-8207-43b4-b4c2-b30da0804382
-- title:
--   Semi Deg Idx: herm Form sum right
-- statement:
--   The Semi Deg Idx construction uses the herm Form sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L11-L18

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : Fin r → K) (w : ι → Fin r → K) :
    S.h u (∑ i ∈ s, w i) = ∑ i ∈ s, S.h u (w i) := by sorry
