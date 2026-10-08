-- Prove2me | Theorems.Thm_ReliableFacilityLoc_LevelOrder_prob_pos_of_assigned
-- name    : ReliableFacilityLoc.LevelOrder.prob_pos_of_assigned
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:17.230426+00:00
-- url     : https://prove2.me/theorems/16b8ed7c-7f65-4593-a109-adaa86cfaea1
-- title:
--   A.2, p. 35 — if every regular $q_k > 0$, an assigned facility has positive serving probability $P_{ijr} > 0$
-- statement:
--   Suppose every regular facility has a positive failure probability, $q_k > 0$ for $0 \le k \le J-1$. Let $(X,Y,P)$ be a feasible solution of (RUFL). Then for every customer $i$, every facility $0 \le j \le J$ (the emergency facility included) and every level $0 \le r \le R$,
--   $$Y_{ijr} = 1 \implies P_{ijr} > 0.$$
--
--   This is the fact that turns the identity of the swap into the strict inequality "$\lambda_i(1-q_k)(d_{ik}-d_{ij})P_{jr} < 0$" of the paper's proof: the cost change of an improving swap is weighted by $P_{ijr}$, and it is strictly negative only if $P_{ijr} > 0$.
--
--   **Formalization Note** The hypothesis $q_k > 0$ is not in the paper, which uses $P_{jr} > 0$ silently. Without it the statement fails: if the level-0 facility has $q = 0$, every later level has $P = 0$ by (1f).
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.2 (proof of Proposition 2), p. 35 (PDF 37), the strict inequality "< 0"; (1e)–(1f), p. 9

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL

open Finset

namespace ReliableFacilityLoc.LevelOrder

/-- **Positivity of the serving probability of an assigned facility** (unnumbered; used for the
strict inequality "`λ_i(1 - q_k)(d_ik - d_ij)P_jr < 0`" in Appendix A.2, p. 35, PDF 37, of Cui,
Ouyang and Shen, *Reliable Facility Location Design under the Risk of Disruptions*,
UCTC-FR-2010-02, Feb. 2010).

If every regular facility has a positive failure probability `q_k > 0`, then in every feasible
solution `(X, Y, P)` of (RUFL), `Y_ijr = 1` implies `P_ijr > 0`, for every facility `j ≤ J`
(including the emergency facility) and every level `r ≤ R`.

Formalization Note: the hypothesis `0 < q k` is not in the paper; without it the statement is false
(if the level-0 facility has `q = 0`, every later level has `P = 0` by (1f)). It is the hypothesis
under which the strict inequality of A.2 holds. -/
theorem prob_pos_of_assigned {I J R : ℕ} (D : Instance I J R) (hq : ∀ k, 0 < D.q k)
    (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (hfeas : D.IsFeasible X Y P)
    (i : Fin I) (j : Fin (J + 1)) (r : Fin (R + 1)) (hj : Y i j r = 1) :
    0 < P i j r := by sorry

end ReliableFacilityLoc.LevelOrder
