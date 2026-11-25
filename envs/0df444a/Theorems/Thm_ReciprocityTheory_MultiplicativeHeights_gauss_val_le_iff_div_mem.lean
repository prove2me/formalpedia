-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_val_le_iff_div_mem
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_val_le_iff_div_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:06.631944+00:00
-- url     : https://prove2.me/theorems/800d35e1-e8e3-5679-9a07-9c905ea443c3
-- title:
--   Multiplicative Heights: gauss val le iff div mem
-- statement:
--   The Multiplicative Heights construction uses the gauss val le iff div mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L8-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_val_le_iff_div_mem {U : Type} [Field U] (V : ValuationSubring U) {x y : U} (hy : y ≠ 0) :
    V.valuation x ≤ V.valuation y ↔ x / y ∈ V := by sorry
