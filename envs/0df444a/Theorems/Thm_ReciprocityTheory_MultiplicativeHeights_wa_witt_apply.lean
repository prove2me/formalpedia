-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_witt_apply
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_witt_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:30.870016+00:00
-- url     : https://prove2.me/theorems/aada757c-044f-4ebf-ad90-4bd2d8de8c4f
-- title:
--   Multiplicative Heights: wa witt apply
-- statement:
--   The Multiplicative Heights construction uses the wa witt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L33-L37

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module

theorem ReciprocityTheory.MultiplicativeHeights.wa_witt_apply {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i j : Fin r) :
    wittMat r m g i j = if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
      else if (i : ℕ) = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0 := by sorry
