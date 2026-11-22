-- Prove2me | Theorems.Thm_ShiTM_exists_stepAux_stack_growth_bound
-- name    : ShiTM.exists_stepAux_stack_growth_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T18:07:43.666711+00:00
-- url     : https://prove2.me/theorems/2fb8b590-f01a-4cad-8547-43da9b5402f2
-- title:
--   A multi-stack machine's stacks grow by at most a fixed amount per step
-- statement:
--   For a finite multi-stack Turing machine there is a single natural number bounding, uniformly over every label, every internal state and every stack configuration, the increase in total stack size caused by executing one step.
--
--   The bound cannot depend on the configuration, so it cannot absorb the existing stack contents; the only way to satisfy it is to bound the number of push operations on any path through any of the machine's finitely many statement trees. A step executes an entire statement tree, so a single step may push many symbols, which is why this is not immediate.
--
--   This is what makes running-time bounds usable for composition: a machine's output cannot be longer than its input plus this constant times the number of steps taken, so the second machine of a composition runs on an input of polynomially bounded length.

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

theorem exists_stepAux_stack_growth_bound {K : Type} [DecidableEq K] [Fintype K]
    {Γ : K → Type} {Λ σ : Type} [Fintype Λ] (M : Λ → Turing.TM2.Stmt Γ Λ σ) :
    ∃ c : ℕ, ∀ (l : Λ) (v : σ) (S : ∀ k, List (Γ k)),
      ∑ k, ((Turing.TM2.stepAux (M l) v S).stk k).length
        ≤ (∑ k, (S k).length) + c := by
  sorry

end ShiTM
