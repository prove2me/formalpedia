-- Prove2me | Theorems.Thm_PochetWolsey_WagnerWhitin_shortest_path_optimal
-- name    : PochetWolsey.WagnerWhitin.shortest_path_optimal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:23.947353+00:00
-- url     : https://prove2.me/theorems/03e74da7-1825-441d-a59c-b2dbbc5dafc7
-- title:
--   Theorem 7.8 — shortest-path LP optimality
-- statement:
--   Let $n\ge1$, let demands $d_t\ge0$, and let $p_t,q_t$ be arbitrary real production and setup costs. Choose $M>0$ with $M\ge\sum_t d_t$. The shortest-path linear program attains its minimum at a point with binary setups:
--   $$\exists (x,y,\varphi)\in Q^{SP-U}:\quad y\in\{0,1\}^n,\quad px+qy=\min_{(x',y',\varphi')\in Q^{SP-U}}(px'+qy').$$
--   The same $(x,y)$ extends by a stock vector to an optimal solution of $LS-U$.
--
--   This states both attainment in the extended formulation and optimality for the original model. Negative setup costs and setups without production are included.
--
--   **Formalization Note** The sufficient finite bound $M\ge\sum_t d_t$ makes the book's “large positive number” precise. Production is nonnegative under the convention documented in F1; initial and final stock are zero. Optimality is a comparison against every feasible point, without an infimum default.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 223 (PDF 237), Theorem 7.8; proof p. 230 (PDF 244)

import Mathlib
import Definitions.Def_PochetWolsey_WagnerWhitin_ShortestPath

open scoped BigOperators

namespace PochetWolsey.WagnerWhitin

theorem shortest_path_optimal (n : ℕ) (hn : 0 < n)
    (d p q : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (M : ℝ) (hMpos : 0 < M) (hM : (∑ t, d t) ≤ M) :
    ∃ z ∈ spFeasible d,
      (∀ t, z.1.2 t = 0 ∨ z.1.2 t = 1) ∧
      (∀ w ∈ spFeasible d, productionCost p q z.1 ≤ productionCost p q w.1) ∧
      ∃ s : Fin (n + 1) → ℝ,
        (z.1.1, z.1.2, s) ∈ lsFeasible d M ∧
        ∀ w ∈ lsFeasible d M,
          productionCost p q z.1 ≤ productionCost p q (w.1, w.2.1) := by sorry

end PochetWolsey.WagnerWhitin
