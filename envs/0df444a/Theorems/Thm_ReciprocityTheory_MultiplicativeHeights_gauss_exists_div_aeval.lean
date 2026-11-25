-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_exists_div_aeval
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_exists_div_aeval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:57.379897+00:00
-- url     : https://prove2.me/theorems/199f360b-9d2d-5749-94b6-0104a595f836
-- title:
--   Multiplicative Heights: gauss exists div aeval
-- statement:
--   The Multiplicative Heights construction uses the gauss exists div aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L13-L24

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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_exists_div_aeval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤) (z : U) :
    ∃ p q : MvPolynomial σ Ω, aeval t q ≠ 0 ∧ z = aeval t p / aeval t q := by sorry
