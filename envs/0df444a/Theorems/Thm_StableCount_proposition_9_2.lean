-- Prove2me | Theorems.Thm_StableCount_proposition_9_2
-- name    : StableCount.proposition_9_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:52:22.167201+00:00
-- url     : https://prove2.me/theorems/dc7c855a-0da9-471b-8994-c286f2f9f094
-- title:
--   Proposition 9.2 — feasible solutions of (P) give admissible sequences of finite sum
-- statement:
--   Let $N\ge 3$ and $M\ge N+2$ be integers. Every feasible solution of (P), extended by $h_d=C/(d(d-1))$ for $d>N$, gives an admissible sequence with finite sum
--   $$
--   S=\sum_{d\ge 1}h_d=\sum_{d=1}^N h_d+\frac CN.
--   $$
--   Consequently, for every $Q\in\mathcal Q$,
--   $$
--   J(Q)\le e^{F_h(Q)}\le e^{nS}.
--   $$
--   This reduces the construction of the weights to a finite convex problem.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: ∑_{d≥1} h_d is finite, or is below ln 2.81 with positive terms → Summable (d ↦ h (d+1)) together with the value of ∑' d, h (d+1); reason: tsum is 0 for a non-summable family, so the sum clause alone would say nothing; a series of positive terms below a bound converges
--   - encoding: λ(t) for t > 0 → lam on all of ℝ, with lam 0 = 0 from Real.log 0 = 0; reason: never hit: for an admissible sequence every argument is positive (p.15)
--   - encoding: (P) minimizes S subject to constraints → IsFeasibleP: the constraints only; reason: the statement is about every feasible solution
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Proposition 9.2, p.32 (PDF p.33); value of S from (27), p.31

import Mathlib
import Definitions.Def_StableCount_Potential
import Definitions.Def_StableCount_FiniteProblem

namespace StableCount

/-- Proposition 9.2 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Proposition 9.2, p.32). Every feasible solution of (P), extended by (26), gives an
admissible sequence with finite sum `S = ∑_{d≥1} h_d`. Consequently, `J(Q) ≤ e^{F_h(Q)} ≤ e^{nS}`.

**Formalization Note** "Finite sum" is `Summable`, and `S` has the value of (27). The indices start at
`d + 1 ≥ 1`: `h 0` is not read. -/
theorem proposition_9_2 (N M : ℕ) (hN : 3 ≤ N) (hM : N + 2 ≤ M) (hs : ℕ → ℝ) (C : ℝ)
    (hP : IsFeasibleP N M hs C) :
    IsAdmissible (extend hs C N) ∧ Summable (fun d => extend hs C N (d + 1)) ∧
    ∑' d, extend hs C N (d + 1) = ∑ d ∈ Finset.Icc 1 N, extend hs C N d + C / (N : ℝ) ∧
    ∀ (n : ℕ) (Q : Member n),
      (Q.J : ℝ) ≤ Real.exp (Q.Fh (extend hs C N)) ∧
      Real.exp (Q.Fh (extend hs C N)) ≤ Real.exp ((n : ℝ) * ∑' d, extend hs C N (d + 1)) := by sorry

end StableCount
