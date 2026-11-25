-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_split
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_dot_split
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:12.132073+00:00
-- url     : https://prove2.me/theorems/9db11f23-0580-4c13-86aa-c15d6cc26473
-- title:
--   Multiplicative Heights: sb dot split
-- statement:
--   The Multiplicative Heights construction uses the sb dot split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L96-L100

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_dot_split (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ w = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) +
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by sorry
