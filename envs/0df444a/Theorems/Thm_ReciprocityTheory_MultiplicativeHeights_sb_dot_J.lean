-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_J
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_dot_J
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:46:26.850881+00:00
-- url     : https://prove2.me/theorems/e4d60363-9526-4902-8e7e-bea9297c9e31
-- title:
--   Multiplicative Heights: sb dot J
-- statement:
--   The Multiplicative Heights construction uses the sb dot J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L102-L105

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_dot_J (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (signMat p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) -
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by sorry
