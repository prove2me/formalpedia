-- Prove2me | Theorems.Thm_PvsNP_NonuniformPrefixDFA_finite_code_one_pass
-- name    : PvsNP.NonuniformPrefixDFA.finite_code_one_pass
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T05:33:40.075718+00:00
-- url     : https://prove2.me/theorems/19f750dd-859b-48a9-8187-17bb3d525891
-- title:
--   A fixed-length finite-code language has a small exact read-once automaton
-- statement:
--   Given a decoder from a finite code set to words of one fixed length L, an exact read-once automaton needs only a position together with a compatible code, or one dead state. Its finite state space has exactly (L+1) times the number of codes plus one states. The transition table may depend on the decoder, and there is one transition per input symbol.
-- source:
--   Finite-state accounting for one-work-tape lower bounds with length-dependent control.

import Mathlib

set_option autoImplicit false

theorem PvsNP.NonuniformPrefixDFA.finite_code_one_pass {B Code : Type*} [Fintype Code] (decode : Code → List B) (length : ℕ)
    (fixed : ∀ c, (decode c).length = length) :
    ∃ (update : Option (Fin (length+1) × Code) → B → Option (Fin (length+1) × Code))
      (initial : Option (Fin (length+1) × Code))
      (accept : Option (Fin (length+1) × Code) → Prop),
      (∀ word, accept (word.foldl update initial) ↔ ∃ c, decode c = word) ∧
      Fintype.card (Option (Fin (length+1) × Code)) = (length+1)*Fintype.card Code+1 := by sorry
