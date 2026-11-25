-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_cover_QI
-- name    : ReciprocityTheory.MultiplicativeHeights.cover_QI
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:26.432971+00:00
-- url     : https://prove2.me/theorems/3ff208ea-7d65-4b5f-8e8d-548d7d65ba4d
-- title:
--   Multiplicative Heights: cover QI
-- statement:
--   The Multiplicative Heights construction uses the cover QI property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LatTest.lean#L144-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LatTest.lean#L144-L167

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatTest
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
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.cover_QI (φ : QI →+* ℂ) (w : ℂ) : ∃ l : QI, IsIntegralElt l ∧ ‖φ l - w‖ ^ 2 ≤ 1 := by sorry
