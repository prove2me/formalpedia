-- Prove2me | Theorems.Thm_ReliableFacilityLoc_LevelOrder_swap_cost_identity
-- name    : ReliableFacilityLoc.LevelOrder.swap_cost_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:44.552807+00:00
-- url     : https://prove2.me/theorems/68860a81-5f1c-41c8-bddb-e0bde70f480a
-- title:
--   A.2, p. 35 — swapping two regular facilities at consecutive levels changes the cost by $\lambda_i(1-q_k)(d_{ik}-d_{ij})P_{ijr}$
-- statement:
--   Let $(X,Y,P)$ be a feasible solution of (RUFL). Suppose customer $i$ is assigned to the regular facility $j$ at level $r$ and to the regular facility $k$ at level $r+1 \le R$, i.e. $Y_{ijr} = Y_{ik,r+1} = 1$. Let $Y'$ be obtained by exchanging $j$ and $k$ between the two levels, and let $P' = P(Y')$ be the probabilities recomputed from (1e)–(1f). Then $(X, Y', P')$ is feasible, and
--   $$\Phi(X,Y',P') - \Phi(X,Y,P) = \lambda_i\,(1-q_k)\,(d_{ik}-d_{ij})\,P_{ijr}.$$
--
--   This is the computation at the heart of the proof of Proposition 2: when $d_{ij} > d_{ik}$, $\lambda_i > 0$ and $P_{ijr} > 0$ the swap strictly lowers the cost, so an optimal solution cannot have its regular facilities out of order.
--
--   **Formalization Note** The paper writes "$< 0$" at the end of the display under its assumption $d_{ij} > d_{ik}$; the identity is stated here without that sign. The hypothesis $j \ne k$ is not needed: it follows from (1c).
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.2 (proof of Proposition 2), pp. 34–35 (PDF 36–37), unnumbered display

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL
import Definitions.Def_ReliableFacilityLoc_LevelOrder_Moves

open Finset

namespace ReliableFacilityLoc.LevelOrder

/-- **Swap cost identity, `k` regular** (unnumbered; Appendix A.2, proof of Proposition 2, pp. 34–35,
PDF 36–37, of Cui, Ouyang and Shen, *Reliable Facility Location Design under the Risk of Disruptions*,
UCTC-FR-2010-02, Feb. 2010).

Let `(X, Y, P)` be feasible for (RUFL), and let customer `i` be assigned to the regular facility `j`
at level `r` and to the regular facility `k` at level `r + 1 ≤ R`. Exchange `j` and `k` between the
two levels (`swapY`), and recompute the probabilities from (1e)–(1f) (`transProb`). The result is
feasible, and its objective differs from that of `(X, Y, P)` by `λ_i (1 - q_k) (d_ik - d_ij) P_ijr`.

Formalization Note: the page's `P′` keeps `P′_hℓs = P_hℓs` at every other index; that array does
not satisfy (1e)–(1f) at the unassigned entries, so here `P′` is the solution of (1e)–(1f) for
`Y′`, which agrees with the page's `P′` wherever `Y′ = 1`. The page concludes "`< 0`" under
`d_ij > d_ik`; the identity is stated here without that sign. `j ≠ k` is not assumed: it follows
from (1c). -/
theorem swap_cost_identity {I J R : ℕ} (D : Instance I J R) (X : Fin J → ℝ)
    (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (hfeas : D.IsFeasible X Y P)
    (i : Fin I) (j k : Fin J) (r : Fin R)
    (hj : Y i j.castSucc r.castSucc = 1) (hk : Y i k.castSucc r.succ = 1) :
    D.IsFeasible X (swapY i j.castSucc k.castSucc r Y)
        (D.transProb (swapY i j.castSucc k.castSucc r Y)) ∧
      D.objective X (swapY i j.castSucc k.castSucc r Y)
          (D.transProb (swapY i j.castSucc k.castSucc r Y)) - D.objective X Y P =
        D.lam i * (1 - D.q k) * (D.d i k - D.d i j) * P i j.castSucc r.castSucc := by sorry

end ReliableFacilityLoc.LevelOrder
