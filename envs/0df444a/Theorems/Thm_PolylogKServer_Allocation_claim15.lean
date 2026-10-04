-- Prove2me | Theorems.Thm_PolylogKServer_Allocation_claim15
-- name    : PolylogKServer.Allocation.claim15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:28:36.790893+00:00
-- url     : https://prove2.me/theorems/ee2b5735-dc4a-4abc-a675-d838a2a0121a
-- title:
--   Claim 15 — the fix-stage inequality Σ_A(y+β) − (1+ε)Σ_A y′ ≤ Σ_A y − Σ_A y′
-- statement:
--   Coordinates are pairs $(i,j)$ with $i\in[d]$ and $j\in\{1,\dots,k\}$. Let $\varepsilon\ge0$ and $\beta=\varepsilon/(1+k)$. Let $\bar y$ be any vector of coordinates and $\bar y'$ a configuration, i.e. $0\le y'_{i,j}\le1$ for all $(i,j)$. If $A$ is a set of coordinates with
--   $$
--   \sum_{(i,j)\in A}y'_{i,j}\ge1\qquad\text{and}\qquad\sum_{i,j}y'_{i,j}\ge kd-k,
--   $$
--   then
--   $$
--   \sum_{(i,j)\in A}(y_{i,j}+\beta)-(1+\varepsilon)\sum_{(i,j)\in A}y'_{i,j}\le\sum_{(i,j)\in A}y_{i,j}-\sum_{(i,j)\in A}y'_{i,j}.
--   $$
--
--   This is the inequality that controls the potential during the fix stage of the paper's fractional allocation algorithm, in the proof of Theorem 14.
--
--   **Formalization Note** The second index runs over `Fin k`, identified with $\{1,\dots,k\}$. The bound $y'\le1$ comes from the definition of a configuration (eq. (3), p. 10). The monotonicity of configurations (eq. (4)) is not assumed; the statement is slightly more general than the paper's.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 23, Claim 15 (β = ε/(1+k) from p. 13; configurations, eq. (3), p. 10)

import Mathlib

namespace PolylogKServer.Allocation

open Finset

/-- **Claim 15** (arXiv:1110.1580v1, p. 23). Coordinates are pairs `(i, j)` with `i ∈ [d]` and
`j ∈ {1, …, k}` (here `Fin d × Fin k`), `ε ≥ 0` and `β = ε / (1 + k)` (p. 13). Let `y` be
arbitrary and let `y'` be a configuration (`0 ≤ y' ≤ 1`, eq. (3)). If `A` is a set of
coordinates with `∑_{(i,j) ∈ A} y'_{i,j} ≥ 1` and `∑_{i,j} y'_{i,j} ≥ kd − k`, then
`∑_A (y_{i,j} + β) − (1 + ε) ∑_A y'_{i,j} ≤ ∑_A y_{i,j} − ∑_A y'_{i,j}`. -/
theorem claim15 (d k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (A : Finset (Fin d × Fin k))
    (y y' : Fin d × Fin k → ℝ) (hy'0 : ∀ z, 0 ≤ y' z) (hy'1 : ∀ z, y' z ≤ 1)
    (hA : 1 ≤ ∑ z ∈ A, y' z) (htot : (k : ℝ) * d - k ≤ ∑ z, y' z) :
    ∑ z ∈ A, (y z + ε / (1 + k)) - (1 + ε) * ∑ z ∈ A, y' z ≤
      ∑ z ∈ A, y z - ∑ z ∈ A, y' z := by sorry

end PolylogKServer.Allocation
