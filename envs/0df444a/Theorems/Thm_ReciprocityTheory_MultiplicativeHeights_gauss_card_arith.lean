-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_card_arith
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_card_arith
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:55.57834+00:00
-- url     : https://prove2.me/theorems/c8f3d8c3-8277-55f3-96ef-a28617e65599
-- title:
--   Multiplicative Heights: gauss card arith
-- statement:
--   The Multiplicative Heights construction uses the gauss card arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L84-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.gauss_card_arith {a b : Cardinal} {s d : ℕ} (h : ((s + d : ℕ) : Cardinal) ≤ a + b)
    (ha : a ≤ d) (hb : b ≤ s) : a = d ∧ b = s := by sorry
