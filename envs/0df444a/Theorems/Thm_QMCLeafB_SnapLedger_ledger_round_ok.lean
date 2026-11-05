-- Prove2me | Theorems.Thm_QMCLeafB_SnapLedger_ledger_round_ok
-- name    : QMCLeafB.SnapLedger.ledger_round_ok
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T10:10:24.4165+00:00
-- url     : https://prove2.me/theorems/6ed316b4-d90c-4613-b461-5cc6020545f7
-- title:
--   Snap displacement versus the recorded margin (margin–ledger joint)
-- statement:
--   A separation loop that runs its oracle at a **snapped** (rational) centre, while its engine's recorded centre is the exact iterate, must account for the displacement when it records the round's margin.
--
--   Let $c$ be the cut normal, $a$ the snapped centre at which the oracle was evaluated, and $a'$ the engine's recorded centre. Suppose the cut separates a set $S$ around $a$ with margin $m$:
--   $$-m \le \langle c, z-a\rangle \quad\text{for all } z\in S.$$
--   Suppose moreover $\lVert c\rVert \le C$ and $\lVert a-a'\rVert \le \varepsilon$. Then Cauchy–Schwarz gives
--   $$\langle c, z-a'\rangle = \langle c, z-a\rangle + \langle c, a-a'\rangle \ge -m - C\varepsilon,$$
--   so the cut separates $S$ around $a'$ with the **inflated** margin $m + C\varepsilon$.
--
--   Consequently the bookkeeping pair a ledger needs for the round holds at `del := m + Cε`: the margin is nonnegative, it fits the quadratic room $\text{del}^2 \le \rho^2\sigma$, and the separation clause holds around the recorded centre.
--
--   The sign matters: the displacement can only *weaken* the guaranteed separation, so the recorded margin must be $m + C\varepsilon$, not $m - C\varepsilon$. Recording the smaller value would be unsound, and the ledger's room must therefore contain the snap cost on top of the oracle's own margin.
-- source:
--   Internal: ellipsoid/separation-loop ledger accounting for the Quantum Max-Cut 0.53 formalisation (BOV rank-three rounding campaign); no external source — elementary Cauchy–Schwarz argument.

import Mathlib
open Finset

theorem QMCLeafB.SnapLedger.ledger_round_ok {k : ℕ} {S : Set (Fin k → ℝ)} {c a a' : Fin k → ℝ} {m C ε rho sigma : ℝ}
    (hsep : ∀ z ∈ S, -m ≤ ∑ i, c i * (z i - a i))
    (hC : Real.sqrt (∑ i, (c i) ^ 2) ≤ C)
    (hε : Real.sqrt (∑ i, (a i - a' i) ^ 2) ≤ ε)
    (hm : 0 < m) (hε0 : 0 ≤ ε) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hroom : (m + C * ε) ^ 2 ≤ rho ^ 2 * sigma) :
    0 ≤ m + C * ε ∧ (m + C * ε) ^ 2 ≤ rho ^ 2 * sigma ∧
      ∀ z ∈ S, -(m + C * ε) ≤ ∑ i, c i * (z i - a' i) := by sorry
