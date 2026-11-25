-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_Dp
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_dot_Dp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:53:33.622513+00:00
-- url     : https://prove2.me/theorems/105a6b91-896b-59c3-a5c1-b3da4983590a
-- title:
--   Multiplicative Heights: sb dot Dp
-- statement:
--   The Multiplicative Heights construction uses the sb dot Dp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L84-L88

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_dot_Dp (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDp p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) := by sorry
