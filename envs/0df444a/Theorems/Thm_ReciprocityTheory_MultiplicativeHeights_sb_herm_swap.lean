-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_herm_swap
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_herm_swap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:46.418584+00:00
-- url     : https://prove2.me/theorems/0669ae60-27d9-49a7-9c05-922a4c9aefb6
-- title:
--   Multiplicative Heights: sb herm swap
-- statement:
--   The Multiplicative Heights construction uses the sb herm swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L80-L82

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
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
open Matrix

theorem ReciprocityTheory.MultiplicativeHeights.sb_herm_swap {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : Mᴴ = M) (v w : Fin r → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by sorry
