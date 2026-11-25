-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_Dn
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_dot_Dn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:45:57.154198+00:00
-- url     : https://prove2.me/theorems/4256aca4-f977-4dfa-bfb1-089f805e0636
-- title:
--   Multiplicative Heights: sb dot Dn
-- statement:
--   The Multiplicative Heights construction uses the sb dot Dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L90-L94

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_dot_Dn (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDn p r *ᵥ w) = star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by sorry
