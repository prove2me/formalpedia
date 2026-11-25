-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_exp_third_lt_two
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:39.190896+00:00
-- url     : https://prove2.me/theorems/91501d1e-92ec-4c28-bf2d-be3a144cb640
-- title:
--   Multiplicative Heights: sb exp third lt two
-- statement:
--   The Multiplicative Heights construction uses the sb exp third lt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L71-L74

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
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
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two : Real.exp (1 / 3) < 2 := by sorry
