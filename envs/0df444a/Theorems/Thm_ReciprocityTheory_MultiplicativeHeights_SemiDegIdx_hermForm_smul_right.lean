-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_smul_right
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_smul_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:55.863728+00:00
-- url     : https://prove2.me/theorems/8ea63c61-6d59-53fc-a22e-2934c962082a
-- title:
--   Semi Deg Idx: herm Form smul right
-- statement:
--   The Semi Deg Idx construction uses the herm Form smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L20-L23

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h u (a • w) = a * S.h u w := by sorry
