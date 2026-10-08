-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_tsp_reformulation
-- name    : SchedComplexity.NoWait.tsp_reformulation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:02:21.218566+00:00
-- url     : https://prove2.me/theorems/dbe3475b-982f-4188-ae81-256f0edde5e3
-- title:
--   No-wait flow shop C_max and ΣC_j as travelling-salesman path problems with weights c_jk (p. 24)
-- statement:
--   Consider a no-wait flow shop with $n$ jobs, $m\ge1$ machines and **strictly positive** processing times $p_{\ell i}$, with $q_{\ell i}$ as in (8) and $c_{jk}$ as in (9). For every $y\in\mathbb N$:
--
--   1. some feasible no-wait schedule has $C_{\max}\le y$ if and only if some ordering $\pi$ of the jobs satisfies
--   $$\sum_{i=1}^{n-1}c_{\pi(i)\pi(i+1)}+q_{\pi(n)m}\le y;$$
--   2. some feasible no-wait schedule has $\sum_\ell C_\ell\le y$ if and only if some ordering $\pi$ satisfies
--   $$\sum_{k=1}^{n}\Bigl(\sum_{i=1}^{k-1}c_{\pi(i)\pi(i+1)}+q_{\pi(k)m}\Bigr)\le y.$$
--
--   Part 1 is the paper's statement that minimizing $C_{\max}$ "is now equivalent to solving the TRAVELLING SALESMAN problem with $V=\{0,\dots,n\}$ and weights $c_{jk}$ defined by (9) and by $c_{0\ell}=0$, $c_{\ell0}=q_{\ell m}$": a tour starting at the dummy vertex $0$ is a job ordering, and its length is the left-hand side. Part 2 is the corresponding fact for the total completion time, which the proof of Theorem 5(b) uses when it says the instance is "constructed as in (a)".
--
--   **Formalization Note** Positivity of the processing times is a hypothesis: with zero processing times one job may pass another, and start order and machine order need not agree. For $n=0$ both sides of both equivalences hold.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 24 (TRAVELLING SALESMAN reformulation after Eq. (9)); p. 25, proof of Theorem 5(b)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop

namespace SchedComplexity.NoWait

/-- The no-wait flow shop as a travelling-salesman problem (p. 24): with strictly positive
processing times, (a) some feasible no-wait schedule has `C_max ≤ y` iff some ordering `π` of
the jobs has path length `Σ_{i<n-1} c_{π i, π (i+1)} + q_{π (n-1), m} ≤ y`, and (b) some feasible
no-wait schedule has `Σ_ℓ C_ℓ ≤ y` iff some ordering `π` has
`Σ_k (Σ_{i<k} c_{π i, π (i+1)} + q_{π k, m}) ≤ y`. -/
theorem tsp_reformulation {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m)
    (hp : ∀ ℓ r, 0 < p ℓ r) (y : ℕ) :
    ((∃ B, IsNoWaitSchedule p B ∧ ∀ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathMakespan p hm π ≤ (y : ℤ)) ∧
      ((∃ B, IsNoWaitSchedule p B ∧ ∑ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathTotalCompletion p hm π ≤ (y : ℤ)) := by sorry

end SchedComplexity.NoWait
