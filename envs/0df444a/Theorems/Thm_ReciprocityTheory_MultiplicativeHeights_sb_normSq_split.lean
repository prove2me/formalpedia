-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_normSq_split
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_normSq_split
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:14.27236+00:00
-- url     : https://prove2.me/theorems/d24cf13a-113f-493d-a7de-145bfc96c876
-- title:
--   Multiplicative Heights: sb norm Sq split
-- statement:
--   The Multiplicative Heights construction uses the sb norm Sq split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallC.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallC.lean#L16-L20

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallC
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
open Matrix Module
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.sb_normSq_split (p : ℕ) {r : ℕ} (v : Fin r → ℂ) : normSq v = posSq p v + negSq p v := by sorry
