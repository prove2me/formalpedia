-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_negSq_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_negSq_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:30.955801+00:00
-- url     : https://prove2.me/theorems/69d3c9ec-2d9b-4635-990f-b3a57422b160
-- title:
--   Multiplicative Heights: sb neg Sq eq
-- statement:
--   The Multiplicative Heights construction uses the sb neg Sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L75-L78

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = normSq (sbDn p r *ᵥ u) := by sorry
