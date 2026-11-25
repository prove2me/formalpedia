-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dn_mul_Dn
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_Dn_mul_Dn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:46:07.677961+00:00
-- url     : https://prove2.me/theorems/f6c251cb-32c3-4fbb-9b42-27bb9cdffc31
-- title:
--   Multiplicative Heights: sb Dn mul Dn
-- statement:
--   The Multiplicative Heights construction uses the sb Dn mul Dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean#L29-L32

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_Dn_mul_Dn (p r : ℕ) : sbDn p r * sbDn p r = sbDn p r := by sorry
