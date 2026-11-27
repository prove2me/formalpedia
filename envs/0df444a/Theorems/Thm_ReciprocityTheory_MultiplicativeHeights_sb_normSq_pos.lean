-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_normSq_pos
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_normSq_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:28.848555+00:00
-- url     : https://prove2.me/theorems/f1b4971a-033b-5632-8c1b-f0aa9aa6d4f7
-- title:
--   Multiplicative Heights: sb norm Sq pos
-- statement:
--   The Multiplicative Heights construction uses the sb norm Sq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L18-L21

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_normSq_pos {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) : 0 < normSq v := by sorry
