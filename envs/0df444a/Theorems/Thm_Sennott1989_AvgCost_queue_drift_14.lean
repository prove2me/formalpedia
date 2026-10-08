-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_queue_drift_14
-- name    : Sennott1989.AvgCost.queue_drift_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:03.924+00:00
-- url     : https://prove2.me/theorems/f3d783ec-141c-4bca-a5bc-a555766fc598
-- title:
--   §3, proof of Proposition 8, (14), p. 631 — the drift of r(i) = Ai^{n+1} is a polynomial of degree ≤ n with leading coefficient A(n + 1)(λ − aβ)
-- statement:
--   Consider the queueing model of Example 2 with finite moment $\lambda^{(n+1)}=\sum_ii^{n+1}p_i<\infty$, a decision $a$ (service rate $a\beta$), a real constant $A$ and the test function $r(i)=Ai^{n+1}$. Then there is a polynomial $\mathcal A$ of degree at most $n$ whose coefficient of $i^n$ is
--   $$A\,(n+1)\,(\lambda-a\beta),\qquad\lambda=\sum_iip_i,$$
--   such that for every state $i\ge1$ the series $\sum_jP_{ij}(a)\big(r(j)-r(i)\big)$ converges and
--   $$\sum_jP_{ij}(a)\big(r(j)-r(i)\big)=\mathcal A(i).\tag{14}$$
--
--   When $\lambda<a\beta$ the drift is eventually below any polynomial of degree $n$ with larger leading coefficient, which is what the drift condition of the Corollary needs.
--
--   **Formalization Note** The identity is for $i\ge1$: state $0$ has its own row $(p_j)$. The paper says "degree $n$"; since the coefficient of $i^n$ vanishes when $\lambda=a\beta$, the statement records degree at most $n$ together with that coefficient. The first line of the paper's display (14) carries a spurious factor $A$; the identity stated here is the correct one.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §3, proof of Proposition 8, (14) and the sentence after it, p. 631

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions
import Definitions.Def_Sennott1989_AvgCost_Queue

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

/-- Sennott (1989), §3, proof of Proposition 8, display (14), p. 631 (unnumbered). Consider the
queueing model of Example 2 with `λ^(n+1) = ∑_i i^{n+1} p_i < ∞`, a decision `x` (serving at
rate `a(x)β`), a real constant `A`, and the test function `r(i) = A i^{n+1}`. Then for every
state `i ≥ 1` the drift `∑_j P_{ij}(x) (r(j) − r(i))` is a (convergent) series whose value is a
polynomial `A(i)` in `i` of degree at most `n` with coefficient of `i^n` equal to
`A (n + 1)(λ − a(x)β)`, where `λ = ∑_i i p_i`.

**Formalization Note** The identity is stated for `i ≥ 1` only: state `0` has its own transition
row `(p_j)`. The paper says "of degree `n` with leading coefficient `A(n + 1)(λ − aβ)`"; when
`λ = aβ` that coefficient is `0`, so the statement records degree `≤ n` and the coefficient of
`i^n`. The paper's first line of (14) carries a spurious factor `A` (typo); the identity here is
the correct one. The paper uses `A` both for the constant and for the polynomial `A(i)`; here the
polynomial is `P`. -/
theorem queue_drift_14 {Act : Type} [Fintype Act] [Nonempty Act] (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act) (A : ℝ) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ q.n ∧
      P.coeff q.n = A * ((q.n : ℝ) + 1) * (q.lam - q.a x * q.β) ∧
      ∀ i : ℕ, 1 ≤ i →
        Summable (fun j : ℕ => (q.toMDC.P i x j).toReal *
          (A * (j : ℝ) ^ (q.n + 1) - A * (i : ℝ) ^ (q.n + 1))) ∧
        ∑' j : ℕ, (q.toMDC.P i x j).toReal *
          (A * (j : ℝ) ^ (q.n + 1) - A * (i : ℝ) ^ (q.n + 1)) = P.eval (i : ℝ) := by sorry

end Sennott1989.AvgCost
