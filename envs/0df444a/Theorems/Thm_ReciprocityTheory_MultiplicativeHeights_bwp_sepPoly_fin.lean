-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_sepPoly_fin
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_sepPoly_fin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:51.436646+00:00
-- url     : https://prove2.me/theorems/587a6fee-adf7-4283-8980-834f27cc9e66
-- title:
--   Multiplicative Heights: bwp sep Poly fin
-- statement:
--   The Multiplicative Heights construction uses the bwp sep Poly fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L38-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L38-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.bwp_sepPoly_fin (k : ℕ) : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) →
    ∃ F : MvPolynomial (Fin n) ℂ, ∀ y, G y = MvPolynomial.eval y F
  := by sorry
