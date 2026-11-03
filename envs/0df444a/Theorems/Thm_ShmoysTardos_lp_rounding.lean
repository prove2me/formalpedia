-- Prove2me | Theorems.Thm_ShmoysTardos_lp_rounding
-- name    : ShmoysTardos.lp_rounding
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T04:08:10.445856+00:00
-- url     : https://prove2.me/theorems/c7ea0e69-26e9-4c09-bc7d-f6418bb72579
-- title:
--   Shmoys–Tardos rounding for GAP: cost at most the LP cost, loads at most $b+p_{\max}$
-- statement:
--   This is the rounding theorem of Shmoys and Tardos for the generalized assignment problem (GAP), in the form cited on p. 11 of Gupta–Kumar–Nagarajan–Shen.
--
--   Let there be $m$ machines and $n$ jobs, with processing times $p_{ij}\ge 0$ and (arbitrary real) assignment costs $c_{ij}$. Let $y=(y_{ij})$ be a feasible solution of the natural LP relaxation with makespan bound $b$:
--   $$y_{ij}\ge 0,\qquad \sum_{i=1}^m y_{ij}=1\ \ (\forall j),\qquad \sum_{j=1}^n p_{ij}\,y_{ij}\le b\ \ (\forall i),$$
--   and let $p_{\max}\ge 0$ be an upper bound on $p_{ij}$ over all pairs with $y_{ij}>0$. Then there is an integral assignment $\sigma:[n]\to[m]$ (job $j$ goes to machine $\sigma(j)$) such that
--
--   1. $\sigma$ only uses pairs in the support of $y$: $y_{\sigma(j)j}>0$ for every job $j$;
--   2. its cost is at most the fractional cost: $\displaystyle\sum_{j} c_{\sigma(j)j}\le \sum_{i,j} c_{ij}\,y_{ij}$;
--   3. every machine load is at most $b+p_{\max}$: $\displaystyle\sum_{j:\sigma(j)=i} p_{ij}\le b+p_{\max}$ for all $i$.
--
--   This is the integral-rounding step used for GAP-type relaxations in scheduling (e.g. step 3 of the rounding procedure in Gupta–Kumar–Nagarajan–Shen, whose Observation 2 applies it with $p_{\max}=1$).
--
--   **Formalization Note** Only the existence of the rounded assignment is stated; the polynomial running time of the algorithm is not modelled. The makespan bound is uniform over machines, as in the cited use. The hypothesis $p_{\max}\ge0$ (automatic when $n\ge1$) only matters when there are no jobs.
-- source:
--   D. B. Shmoys and É. Tardos, An approximation algorithm for the generalized assignment problem, Math. Programming 62 (1993) 461–474, §2 (rounding theorem); as cited in Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 11 (§3.2, paragraph after step 3) and p. 12 (proof of Observation 2)

import Mathlib

namespace ShmoysTardos

/-- Shmoys–Tardos rounding for the generalized assignment problem: a fractional assignment
`y` of `n` jobs to `m` machines with fractional cost `Σ c_{ij} y_{ij}` and fractional loads
`Σ_j p_{ij} y_{ij} ≤ b` can be rounded to an integral assignment `σ`, using only pairs with
`y_{ij} > 0`, of cost at most the fractional cost and with every load at most `b + p_max`,
where `p_max` bounds `p_{ij}` on the support of `y`. -/
theorem lp_rounding {m n : ℕ} (p c : Fin m → Fin n → ℝ) (b pmax : ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (y : Fin m → Fin n → ℝ) (hy0 : ∀ i j, 0 ≤ y i j)
    (hy1 : ∀ j, ∑ i, y i j = 1) (hload : ∀ i, ∑ j, p i j * y i j ≤ b)
    (hpmax0 : 0 ≤ pmax) (hpmax : ∀ i j, 0 < y i j → p i j ≤ pmax) :
    ∃ σ : Fin n → Fin m, (∀ j, 0 < y (σ j) j) ∧
      ∑ j, c (σ j) j ≤ ∑ i, ∑ j, c i j * y i j ∧
      ∀ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), p i j ≤ b + pmax := by sorry

end ShmoysTardos
