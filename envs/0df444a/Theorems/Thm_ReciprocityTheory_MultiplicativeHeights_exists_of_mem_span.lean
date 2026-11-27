-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_of_mem_span
-- name    : ReciprocityTheory.MultiplicativeHeights.exists_of_mem_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:15.085171+00:00
-- url     : https://prove2.me/theorems/a05a33b0-e587-5937-bbac-b1473890388f
-- title:
--   Multiplicative Heights: exists of mem span
-- statement:
--   The Multiplicative Heights construction uses the exists of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L92-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L92-L117

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset

theorem ReciprocityTheory.MultiplicativeHeights.exists_of_mem_span {ι κ : Type*} (F : MvPolynomial ι ℂ) (m : κ → (ι →₀ ℕ)) (A : Set κ)
    (y : MvPolynomial ι ℂ)
    (hy : y ∈ Submodule.span ℂ ((fun j => F * MvPolynomial.monomial (m j) (1 : ℂ)) '' A)) :
    ∃ Q : MvPolynomial ι ℂ, y = F * Q ∧ (Q.support : Set (ι →₀ ℕ)) ⊆ m '' A := by sorry
