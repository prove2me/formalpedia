-- Prove2me | Theorems.Thm_SennottDP_SEN_lemma_7_2_1_acoi_bound
-- name    : SennottDP.SEN.lemma_7_2_1_acoi_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:17:52.947434+00:00
-- url     : https://prove2.me/theorems/02ff76b9-7fea-45d7-a68f-06b871e10fa8
-- title:
--   Lemma 7.2.1 — a bounded-below solution of the ACOI for a stationary policy bounds its average cost
-- statement:
--   Let $e$ be a stationary policy. Assume there exist a finite constant $J$ and a finite function $h$ on $S$, bounded below, such that
--
--   $$J + h(i) \ge C(i,e(i)) + \sum_j P_{ij}(e(i))\, h(j), \qquad i \in S. \qquad (7.4)$$
--
--   Then $J_e(i) \le J$ for every $i \in S$.
--
--   This is the verification step of the average cost theory: a supersolution of the average cost optimality inequality for a single stationary policy bounds that policy's average cost.
--
--   **Formalization Note** $J \in \mathbb R$ and $h : S \to \mathbb R$; the sum is the extended real $\sum_j P_{ij}h^+ - \sum_j P_{ij}h^-$ (finite negative part because $h$ is bounded below), and the comparison $J_e(i) \le J$ is made in `EReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 133, Lemma 7.2.1, (7.4)

import Mathlib
import Definitions.Def_SennottDP_SEN_Criteria

open scoped ENNReal NNReal

namespace SennottDP.SEN

/-- Sennott (1999), Lemma 7.2.1, p. 133: let `e` be a stationary policy. Assume there exist a
(finite) constant `J` and a (finite) function `h` that is bounded below in `i` such that
`J + h(i) ≥ C(i,e) + ∑_j P_{ij}(e) h(j)` for `i ∈ S` (7.4). Then `J_e(i) ≤ J` for `i ∈ S`.
The sum `∑_j P_{ij}(e) h(j)` is `wsum` (well defined in `(−∞, ∞]` since `h` is bounded below);
the comparison `J_e(i) ≤ J` is made in `EReal`, since `J_e(i) ∈ [0, ∞]` and `J ∈ ℝ`. -/
theorem lemma_7_2_1_acoi_bound {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act)
    (e : StationaryPolicy M) (J : ℝ) (h : S → ℝ) (hbdd : BddBelow (Set.range h))
    (h74 : ∀ i, ((M.C i (e.1 i) : ℝ) : EReal) + wsum (M.P i (e.1 i)) h ≤ ((J + h i : ℝ) : EReal)) :
    ∀ i, (avgCost M e.toPolicy i : EReal) ≤ (J : EReal) := by sorry

end SennottDP.SEN
