-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dp_herm
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_Dp_herm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:44.082796+00:00
-- url     : https://prove2.me/theorems/5a724f1a-e534-5092-ab64-8b5a9165db8c
-- title:
--   Multiplicative Heights: sb Dp herm
-- statement:
--   The Multiplicative Heights construction uses the sb Dp herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L46-L50

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_Dp_herm (p r : ℕ) : (sbDp p r)ᴴ = sbDp p r := by sorry
