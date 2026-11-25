-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_aeval_mem
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_aeval_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:03.533328+00:00
-- url     : https://prove2.me/theorems/928cf915-e1ae-45e7-8103-c62a408a9119
-- title:
--   Multiplicative Heights: gauss aeval mem
-- statement:
--   The Multiplicative Heights construction uses the gauss aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L95-L99

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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_aeval_mem {B C : Type} [CommRing B] [CommRing C] [Algebra B C] {σ : Type}
    (g : σ → C) (P : MvPolynomial σ B) (R : Subring C)
    (hc : ∀ α, algebraMap B C (P.coeff α) ∈ R) (hg : ∀ s, g s ∈ R) : aeval g P ∈ R := by sorry
