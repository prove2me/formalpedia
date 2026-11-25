-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dn_herm
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_Dn_herm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:11:29.751492+00:00
-- url     : https://prove2.me/theorems/4d2d8810-a751-5906-b01a-fddfadf4bca4
-- title:
--   Multiplicative Heights: sb Dn herm
-- statement:
--   The Multiplicative Heights construction uses the sb Dn herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L52-L56

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_Dn_herm (p r : ℕ) : (sbDn p r)ᴴ = sbDn p r := by sorry
