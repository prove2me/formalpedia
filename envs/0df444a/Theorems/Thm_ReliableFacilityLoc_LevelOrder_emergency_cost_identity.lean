-- Prove2me | Theorems.Thm_ReliableFacilityLoc_LevelOrder_emergency_cost_identity
-- name    : ReliableFacilityLoc.LevelOrder.emergency_cost_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:50.753167+00:00
-- url     : https://prove2.me/theorems/fe7a4473-ed5b-4ad3-bb7d-59692a6dd97b
-- title:
--   A.2, p. 35 — moving the emergency facility up one level and dropping $j$ changes the cost by $\lambda_i P_{ijr}(\phi_i - d_{ij})$
-- statement:
--   Let $(X,Y,P)$ be a feasible solution of (RUFL). Suppose customer $i$ is assigned to the regular facility $j$ at level $r$ and to the emergency facility $J$ at level $r+1 \le R$, i.e. $Y_{ijr} = Y_{iJ,r+1} = 1$. Let $Y'$ be obtained by assigning $J$ at level $r$ in place of $j$ and dropping $j$ (so $Y'_{iJ,r+1} = Y'_{ij,r+1} = 0$), and let $P' = P(Y')$ be the probabilities recomputed from (1e)–(1f). Then $(X,Y',P')$ is feasible, and
--   $$\Phi(X,Y',P') - \Phi(X,Y,P) = \lambda_i\,P_{ijr}\,(\phi_i - d_{ij}) \qquad\text{(computed from (1f))}.$$
--
--   This is the case $k = J$ of the proof of Proposition 2: if $d_{ij} > d_{iJ} = \phi_i$, $\lambda_i > 0$ and $P_{ijr} > 0$, the move strictly lowers the cost.
--
--   **Formalization Note** The page does not print this value; it says only that the case $k = J$ "is similar, except that $Y'_{ij,r+1} = P'_{ij,r+1} = 0$, which reduces the cost even more". The explicit difference follows from (1e)–(1f): the emergency facility at level $r$ has $P'_{iJr} = P_{ijr}/(1-q_j)$ and the removed level-$(r+1)$ term had $P_{iJ,r+1} = q_j P_{ijr}/(1-q_j)$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.2 (proof of Proposition 2), p. 35 (PDF 37), case k = J

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL
import Definitions.Def_ReliableFacilityLoc_LevelOrder_Moves

open Finset

namespace ReliableFacilityLoc.LevelOrder

/-- **Emergency case `k = J`** (unnumbered; Appendix A.2, proof of Proposition 2, p. 35, PDF 37, of
Cui, Ouyang and Shen, *Reliable Facility Location Design under the Risk of Disruptions*,
UCTC-FR-2010-02, Feb. 2010).

Let `(X, Y, P)` be feasible for (RUFL), and let customer `i` be assigned to the regular facility `j`
at level `r` and to the emergency facility `J` at level `r + 1 ≤ R`. Move `J` up to level `r` and
drop `j` (`emergencyUpY`), recomputing the probabilities from (1e)–(1f) (`transProb`). The result is
feasible, and its objective differs from that of `(X, Y, P)` by `λ_i P_ijr (φ_i - d_ij)`.

Formalization Note: the page states only that this case "is similar, except that
`Y′_{ij,r+1} = P′_{ij,r+1} = 0`, which reduces the cost even more". The explicit change
`λ_i P_ijr (φ_i - d_ij)` is computed from (1e)–(1f): the emergency facility at level `r` has
`P′_iJr = P_ijr / (1 - q_j)`, and the removed level-`r+1` term had `P_{iJ,r+1} = q_j P_ijr / (1 - q_j)`. -/
theorem emergency_cost_identity {I J R : ℕ} (D : Instance I J R) (X : Fin J → ℝ)
    (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (hfeas : D.IsFeasible X Y P)
    (i : Fin I) (j : Fin J) (r : Fin R)
    (hj : Y i j.castSucc r.castSucc = 1) (hJ : Y i (Fin.last J) r.succ = 1) :
    D.IsFeasible X (emergencyUpY i j.castSucc r Y)
        (D.transProb (emergencyUpY i j.castSucc r Y)) ∧
      D.objective X (emergencyUpY i j.castSucc r Y)
          (D.transProb (emergencyUpY i j.castSucc r Y)) - D.objective X Y P =
        D.lam i * P i j.castSucc r.castSucc * (D.phi i - D.d i j) := by sorry

end ReliableFacilityLoc.LevelOrder
