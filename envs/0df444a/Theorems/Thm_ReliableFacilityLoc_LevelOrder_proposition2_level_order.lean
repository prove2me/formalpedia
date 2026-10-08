-- Prove2me | Theorems.Thm_ReliableFacilityLoc_LevelOrder_proposition2_level_order
-- name    : ReliableFacilityLoc.LevelOrder.proposition2_level_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:20.171648+00:00
-- url     : https://prove2.me/theorems/2338a159-443a-4b12-94a4-2cc8c83353f8
-- title:
--   Proposition 2 — in any optimal solution of (RUFL), each customer's consecutive levels are ordered by distance, $d_{ij} \le d_{ik}$
-- statement:
--   Consider the reliability uncapacitated facility location problem (RUFL) with positive demand rates $\lambda_i > 0$ and positive failure probabilities $q_k > 0$ at every regular site. Let $(X,Y,P)$ be an optimal solution. If customer $i$ is assigned to facility $j$ at level $r$ and to facility $k$ at level $r+1$, that is
--   $$Y_{ijr} = 1 \quad\text{and}\quad Y_{ik,r+1} = 1 \qquad (0 \le r,\ r+1 \le R),$$
--   then
--   $$d_{ij} \le d_{ik},$$
--   where $j$ and $k$ range over all facilities $0,\dots,J$ and $d_{iJ} = \phi_i$ for the emergency facility.
--
--   In words: although (RUFL) does not force a customer to be served by her closer facilities first, every optimal solution assigns her facilities level by level in nondecreasing order of distance, with the emergency facility (cost $\phi_i$) after every regular facility that is no more expensive. This extends the equal-failure-probability result of Snyder and Daskin to site-dependent failure probabilities, and it means that the optimal assignment levels depend only on the distances, given the set of facilities assigned to a customer.
--
--   **Formalization Note** The paper states Proposition 2 without the hypotheses $\lambda_i > 0$ and $q_k > 0$; as printed it is false. With one customer, $\lambda = 1$, three sites with $f = 0$, $d = (1, 5, 3)$, $q = (0, \tfrac12, \tfrac12)$, $\phi = 100$ and $R = 3$, the site never fails at level 0, every later level has $P = 0$, and the assignment order $(0, 1, 2)$ is optimal although $d_{i1} = 5 > 3 = d_{i2}$. Demand $\lambda_i = 0$ likewise makes customer $i$'s order irrelevant. The paper's proof needs both hypotheses for its strict inequality. The printed range "$0 \le r \le R$" is read as $r + 1 \le R$, the range in which $Y_{ik,r+1}$ exists.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 10 (PDF 12), Proposition 2; proof in Appendix A.2, pp. 34–35 (PDF 36–37); hypotheses λ_i > 0, q_k > 0 added

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL

open Finset

namespace ReliableFacilityLoc.LevelOrder

/-- **Proposition 2** (p. 10, PDF 12) of Cui, Ouyang and Shen, *Reliable Facility Location Design
under the Risk of Disruptions*, UCTC-FR-2010-02, Feb. 2010. Printed:
"In any optimal solution (X,Y,P) of (RUFL), if Y_ijr = 1 and Y_ik,r+1 = 1, then d_ij ≤ d_ik, for all
0 ≤ i ≤ I − 1, 0 ≤ j ≤ J, and 0 ≤ r ≤ R."

Assume every demand rate is positive (`λ_i > 0`) and every regular facility has a positive failure
probability (`q_k > 0`). Then in every optimal solution `(X, Y, P)` of (RUFL), if customer `i` is
assigned to facility `j` at level `r` and to facility `k` at level `r + 1 ≤ R`, then
`d_ij ≤ d_ik`, where `d_iJ = φ_i` for the emergency facility (`j`, `k` range over all `J + 1`
facilities).

Formalization Note: the hypotheses `0 < lam i` and `0 < q k` are added. As printed the proposition
is false: with one customer, `λ = 1`, three sites with `f = 0`, `d = (1, 5, 3)`, `q = (0, 1/2, 1/2)`, `φ = 100` and `R = 3`, the level-0 facility
never fails, every later level has `P = 0`, and the orders `(0, 1, 2)` and `(0, 2, 1)` have the same
cost, so an optimal solution may list its backups out of order; `λ_i = 0` likewise makes customer
`i`'s order irrelevant. The paper's proof needs `P_ijr > 0` and `λ_i > 0` for its "`< 0`".
The level `r` is `r : Fin R`, encoding `0 ≤ r` and `r + 1 ≤ R`, the range in which `Y_{ik,r+1}`
exists. -/
theorem proposition2_level_order {I J R : ℕ} (D : Instance I J R)
    (hlam : ∀ i, 0 < D.lam i) (hq : ∀ k, 0 < D.q k)
    (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (hopt : D.IsOptimal X Y P)
    (i : Fin I) (j k : Fin (J + 1)) (r : Fin R)
    (hj : Y i j r.castSucc = 1) (hk : Y i k r.succ = 1) :
    D.dExt i j ≤ D.dExt i k := by sorry

end ReliableFacilityLoc.LevelOrder
