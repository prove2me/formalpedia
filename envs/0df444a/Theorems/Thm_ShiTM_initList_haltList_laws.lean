-- Prove2me | Theorems.Thm_ShiTM_initList_haltList_laws
-- name    : ShiTM.initList_haltList_laws
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T13:55:22.717987+00:00
-- url     : https://prove2.me/theorems/adabe404-9532-456d-8ce1-1a4c04c4c3c2
-- title:
--   Basic laws for the initial and halting configurations of a multi-stack machine
-- statement:
--   For a finite multi-stack Turing machine, the initial configuration on an input list has label the machine's entry label, internal state the initial state, the input list on the designated input stack, and every other stack empty; and the halting configuration on an output list has no label, internal state the initial state, the output list on the designated output stack, and every other stack empty.
--
--   These are the defining properties, but the library states none of them: the configurations are given by a dependent if-then-else whose positive branch transports along an equality of stack indices, so even reading off the contents of the designated stack requires collapsing that transport. Every argument about sequencing two machines needs these facts.

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

theorem initList_haltList_laws (tm : Turing.FinTM2)
    (s : List (tm.Γ tm.k₀)) (t : List (tm.Γ tm.k₁)) :
    (Turing.initList tm s).l = Option.some tm.main
      ∧ (Turing.initList tm s).var = tm.initialState
      ∧ (Turing.initList tm s).stk tm.k₀ = s
      ∧ (∀ k : tm.K, k ≠ tm.k₀ → (Turing.initList tm s).stk k = [])
      ∧ (Turing.haltList tm t).l = Option.none
      ∧ (Turing.haltList tm t).var = tm.initialState
      ∧ (Turing.haltList tm t).stk tm.k₁ = t
      ∧ (∀ k : tm.K, k ≠ tm.k₁ → (Turing.haltList tm t).stk k = []) := by
  sorry

end ShiTM
