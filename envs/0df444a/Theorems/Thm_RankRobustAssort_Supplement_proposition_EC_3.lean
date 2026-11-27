-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_proposition_EC_3
-- name    : RankRobustAssort.Supplement.proposition_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:38:31.280458+00:00
-- url     : https://prove2.me/theorems/59ae4cfa-fb2c-45f3-b2af-52c92941aab3
-- title:
--   Proposition EC.3 — the best-case revenue equals the optimal value of the linear program (EC.66)
-- statement:
--   For each assortment $S\in\mathcal S$, the best-case expected revenue $\max_{\lambda\in\mathcal U}\mathscr R^\lambda(S)$ is equal to the optimal objective value of the linear optimization problem
--
--   $$
--   \begin{aligned}
--   \max_{\lambda,\epsilon}\ &\sum_{(i_1,\dots,i_M)\in\mathcal L}\xi_{i_1\cdots i_M}(S)\,\lambda_{i_1\cdots i_M}\\
--   \text{s.t. }&\sum_{(i_1,\dots,i_M)\in\mathcal L:\ i_m=i}\lambda_{i_1\cdots i_M}-\epsilon_{m,i}=v_{m,i}\quad\forall m\in\mathcal M,\ i\in S_m,\\
--   &\sum_{(i_1,\dots,i_M)\in\mathcal L}\lambda_{i_1\cdots i_M}=1,\qquad\|\epsilon\|\le\eta,\qquad\lambda_{i_1\cdots i_M}\ge0\ \ \forall(i_1,\dots,i_M)\in\mathcal L.
--   \end{aligned}
--   \tag{EC.66}
--   $$
--
--   This is the optimistic counterpart of Proposition 1. Since the constraints do not depend on $S$, comparing assortments for (OO) reduces to comparing the coefficients $\xi_{i_1\cdots i_M}(S)$.
--
--   **Formalization Note.** The consistent set $\mathcal U$ is assumed nonempty, the paper's standing assumption.
--
--   Differences from the source:
--   - encoding: $\max_{\lambda\in\mathcal U}$ and the optimal value of (EC.66) → suprema of the corresponding value sets; reason: under $\mathcal U\ne\emptyset$ both sets are nonempty and bounded and the suprema are attained, so they are the paper's maxima
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition EC.3, p.ec54

import Mathlib
import Definitions.Def_RankRobustAssort_Supplement_bestCase
import Definitions.Def_RankRobustAssort_Supplement_lpMaxValue

namespace RankRobustAssort.Supplement

/-- **Proposition EC.3.** For each `S ∈ 𝒮`, `max_{λ∈𝒰} ℛ^λ(S)` is equal to the optimal objective
value of the linear optimization problem (EC.66).

Sturt, arXiv:2112.05010v4, Proposition EC.3, p.ec54.

Formalization Note: `S ∈ 𝒮` is `0 ∈ S`. The paper's standing assumption `𝒰 ≠ ∅` (p.8) is the
hypothesis `hU`; under it both sides are attained maxima (see `bestCase`, `lpMaxValue`). -/
theorem proposition_EC_3 {n M : ℕ} (P : Problem n M) (hU : (consistentSet P).Nonempty)
    (S : Finset (Fin (n + 1))) (hS : 0 ∈ S) :
    bestCase P S = lpMaxValue P S := by sorry

end RankRobustAssort.Supplement
