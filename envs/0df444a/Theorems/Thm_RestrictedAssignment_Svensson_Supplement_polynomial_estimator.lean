-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_Supplement_polynomial_estimator
-- name    : RestrictedAssignment.Svensson.Supplement.polynomial_estimator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:58:53.629013+00:00
-- url     : https://prove2.me/theorems/2c256fb0-1736-45fc-a892-12cc43786408
-- title:
--   Theorem 1.1 — polynomial-time estimation of optimal makespan
-- statement:
--   Fix any real $\varepsilon>0$. There exist one deterministic finite Turing program $A$ and positive integer coefficient $C$ and degree $k\ge0$, which may depend on $\varepsilon$, such that for every feasible binary restricted-assignment instance $I$ of encoded length $n$, the program halts with a rational lower estimate $L$ and
--   $$\mathrm{time}_A(I)\le C(n+1)^k,\qquad 0\le L\le\mathrm{OPT}(I)\le(33/17+\varepsilon)L.$$
--   The program is uniform over all job counts, machine counts, eligibility lists and rational bit lengths. If OPT is zero, its output is exactly zero. The specification concerns numerical estimation; no polynomial-time schedule construction is asserted.
--
--   This is the computational companion to the published integrality-gap goal. Runtime is derived from actual machine transitions and includes the encoded output; neither a suitable estimator nor a configuration-LP oracle is assumed.
--
--   Differences from the source:
--   - encoding: polynomial-time estimation on restricted-assignment instances → a deterministic finite multi-stack Turing machine on binary counts, eligibility lists and nonnegative rational sizes, with runtime C(n+1)^k on the feasible-instance domain; reason: the standard finite-input interpretation; arbitrary bit lengths and all feasible finite instances are retained, with no oracle or supplied cost
--   - reading: estimates the optimum within 33/17 + ε → a rational lower estimate L with 0 ≤ L ≤ OPT ≤ (33/17 + ε)L, for every fixed positive real ε; reason: pp. 2–3 explicitly describe a polynomial-time computable lower bound; the program and polynomial constants may depend on the fixed tolerance
--   - encoding: minimum makespan of an eligible schedule → the actual finite minimum is some OPT; empty-job optimum is 0, and infeasible instances return none; reason: prevents an empty real infimum from becoming a spurious zero; the theorem promises output only on feasible instances
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_Supplement_estimation

namespace RestrictedAssignment.Svensson.Supplement

/-- Svensson, arXiv:1011.1168v2, p. 2, Theorem 1.1; pp. 3–4 and 11 explain
approximate solution of [C-LP]. One deterministic finite machine, coefficient,
and degree for each fixed real tolerance; all encoded instance lengths allowed. -/
theorem polynomial_estimator (ε : ℝ) (hε : 0 < ε) :
    ∃ A : IntConeFPT.Machine, ∃ C k : ℕ, 0 < C ∧
      ∀ I : BinaryInstance, I.Feasible → ∃ L : ℚ,
        IsEstimate I ε L ∧
        IntConeFPT.RunsWithin A I.code (estimateCode L)
          ((C : ℝ) * ((I.code.length : ℝ) + 1) ^ k) := by sorry

end RestrictedAssignment.Svensson.Supplement
