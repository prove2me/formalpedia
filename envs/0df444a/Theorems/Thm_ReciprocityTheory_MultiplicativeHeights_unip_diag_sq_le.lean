-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_diag_sq_le
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_diag_sq_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:32.789888+00:00
-- url     : https://prove2.me/theorems/e35468df-b929-4533-884d-66fa3243f1d8
-- title:
--   Multiplicative Heights: unip diag sq le
-- statement:
--   The Multiplicative Heights construction uses the unip diag sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L34-L41

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix

theorem ReciprocityTheory.MultiplicativeHeights.unip_diag_sq_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (i : Fin r) :
    ‖(A ^ n) i i‖ ^ 2 ≤ c ^ n := by sorry
