-- Prove2me | Theorems.Thm_SPHardness_OrderPolytope_lemma_3
-- name    : SPHardness.OrderPolytope.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:03.485002+00:00
-- url     : https://prove2.me/theorems/99a9b052-77ce-4066-a1fa-d5358458e7bc
-- title:
--   Lemma 3, pp. 10–11 — accurate order-polytope volume yields the linear-extension count
-- statement:
--   Let $P$ be a finite poset with $k=|P|$, volume $V(P)$, and linear-extension count $N(P)$. If $\vartheta$ approximates $V(P)$ with absolute error at most $\varepsilon$, where $0\le\varepsilon<1/(2k!)$, then
--
--   $$
--   \left|k!\,\vartheta-N(P)\right|<\frac12.
--   $$
--
--   Therefore $N(P)$ is the unique integer nearest to $k!\vartheta$. This is the rounding step of the reduction from #LinearExtension to order-polytope volume approximation.
--
--   **Formalization Note** The theorem records reduction correctness; it does not formalize #P-hardness or the polynomial-time cost of the remaining steps. The strict accuracy threshold rules out rounding ties.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), pp. 10–11, Lemma 3 and its proof. https://optimization-online.org/wp-content/uploads/2015/03/4825.pdf

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

namespace SPHardness.OrderPolytope

open scoped Nat

/-- The rounding step in Lemma 3. -/
theorem lemma_3 (P : Type) [Fintype P] [PartialOrder P]
    (ϑ ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / (2 * ((Fintype.card P)! : ℝ)))
    (hϑ : |ϑ - volOrder P| ≤ ε) :
    |((Fintype.card P)! : ℝ) * ϑ - numLinExt P| < 1 / 2 := by sorry

end SPHardness.OrderPolytope
