-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_normOrd_le_span_sup
-- name    : ReciprocityTheory.MultiplicativeHeights.normOrd_le_span_sup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:32.120836+00:00
-- url     : https://prove2.me/theorems/676b7d37-046c-4d34-83b7-d7287fb02b16
-- title:
--   Multiplicative Heights: norm Ord le span sup
-- statement:
--   The Multiplicative Heights construction uses the norm Ord le span sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/NormOrdLengthResidue.lean#L33-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/NormOrdLengthResidue.lean#L33-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_NormOrdLengthResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module

theorem ReciprocityTheory.MultiplicativeHeights.normOrd_le_span_sup {B : Type} [CommRing B] [IsDedekindDomain B] {P : Ideal B}
    [hP : P.IsMaximal] (hP0 : P ≠ ⊥) {n : ℕ} {a : B} (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) :
    P ^ n ≤ Ideal.span {a} ⊔ P ^ (n + 1) := by sorry
