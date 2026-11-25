-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_ballRatio_nonneg
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:28.207406+00:00
-- url     : https://prove2.me/theorems/f1c8f264-b265-4843-b577-022fb1ae66f3
-- title:
--   Multiplicative Heights: sb ball Ratio nonneg
-- statement:
--   The Multiplicative Heights construction uses the sb ball Ratio nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L47-L53

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg {r : ℕ} (hr : 0 < r) : 0 ≤ ballRatio r := by sorry
