-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_normOrd_length_pow
-- name    : ReciprocityTheory.MultiplicativeHeights.normOrd_length_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:24.989801+00:00
-- url     : https://prove2.me/theorems/b92dd7c9-7a9d-4923-98a7-93bf0f2dfc64
-- title:
--   Multiplicative Heights: norm Ord length pow
-- statement:
--   The Multiplicative Heights construction uses the norm Ord length pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/NormOrdLengthResidue.lean#L123-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/NormOrdLengthResidue.lean#L123-L136

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

theorem ReciprocityTheory.MultiplicativeHeights.normOrd_length_pow (O B : Type) [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (P : Ideal B) [P.IsMaximal] (hP0 : P ≠ ⊥) (n : ℕ) :
    length O (B ⧸ P ^ n) = n * length O (B ⧸ P) := by sorry
