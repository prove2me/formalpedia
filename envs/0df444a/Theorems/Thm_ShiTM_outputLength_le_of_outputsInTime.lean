-- Prove2me | Theorems.Thm_ShiTM_outputLength_le_of_outputsInTime
-- name    : ShiTM.outputLength_le_of_outputsInTime
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T18:51:39.320156+00:00
-- url     : https://prove2.me/theorems/ed2e4548-2f17-489d-bd7d-4b304b73c2e0
-- title:
--   A machine's output is no longer than its input plus a constant times its running time
-- statement:
--   Suppose one step of a multi-stack machine increases total stack size by at most a fixed constant, uniformly over labels, states and configurations. Then whenever the machine, started on an input, halts within a given number of steps with some output, the output's length is at most the input's length plus that constant times the step bound.
--
--   A machine cannot emit more than it has room to write, and it gains room only by pushing. This is what makes running-time bounds composable: the second machine of a sequential composition runs on the first machine's output, so its own polynomial bound is evaluated at an argument that this result shows to be polynomially bounded in the original input length. Without it no polynomial bound on a composite exists at all.

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Option.Basic
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false

attribute [local instance] Turing.FinTM2.kFin

namespace ShiTM

theorem outputLength_le_of_outputsInTime {tm : Turing.FinTM2} (c : ℕ)
    (hc : ∀ (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
      ∑ k, ((Turing.TM2.stepAux (tm.m l) v S).stk k).length ≤ (∑ k, (S k).length) + c)
    (s : List (tm.Γ tm.k₀)) (t : List (tm.Γ tm.k₁)) (m : ℕ)
    (h : Turing.TM2OutputsInTime tm s (Option.some t) m) :
    t.length ≤ s.length + c * m := by
  sorry

end ShiTM
