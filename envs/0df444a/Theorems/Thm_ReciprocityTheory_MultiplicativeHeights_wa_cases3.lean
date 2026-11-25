-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_cases3
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_cases3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:09.580857+00:00
-- url     : https://prove2.me/theorems/798e91ea-2a65-4038-96dd-57e4ff757822
-- title:
--   Multiplicative Heights: wa cases3
-- statement:
--   The Multiplicative Heights construction uses the wa cases3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L9-L16

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

theorem ReciprocityTheory.MultiplicativeHeights.wa_cases3 {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j : Fin n, i = (Fin.castSucc j).succ := by sorry
