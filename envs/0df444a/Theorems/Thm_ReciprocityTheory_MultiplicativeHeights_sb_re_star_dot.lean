-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_re_star_dot
-- name    : ReciprocityTheory.MultiplicativeHeights.sb_re_star_dot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:42.306599+00:00
-- url     : https://prove2.me/theorems/e357b460-192f-5592-bc65-8f316a94c8e0
-- title:
--   Multiplicative Heights: sb re star dot
-- statement:
--   The Multiplicative Heights construction uses the sb re star dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallA.lean#L11-L16

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

theorem ReciprocityTheory.MultiplicativeHeights.sb_re_star_dot {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = normSq v := by sorry
