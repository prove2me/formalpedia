-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_card_degree_le
-- name    : ReciprocityTheory.MultiplicativeHeights.card_degree_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:42.470645+00:00
-- url     : https://prove2.me/theorems/809581a7-bbba-5366-8dd1-3ad184fc74a0
-- title:
--   Multiplicative Heights: card degree le
-- statement:
--   The Multiplicative Heights construction uses the card degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/FinrankRestrictTotalDegree.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/FinrankRestrictTotalDegree.lean#L39-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights

theorem ReciprocityTheory.MultiplicativeHeights.card_degree_le (D e : ℕ) :
    Nat.card {α : Fin D →₀ ℕ // α.degree ≤ e} = (e + D).choose D := by sorry
