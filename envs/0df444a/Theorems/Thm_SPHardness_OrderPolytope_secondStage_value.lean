-- Prove2me | Theorems.Thm_SPHardness_OrderPolytope_secondStage_value
-- name    : SPHardness.OrderPolytope.secondStage_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:18.134009+00:00
-- url     : https://prove2.me/theorems/2513392a-1fb4-4fb2-82c8-c52669ba1b5b
-- title:
--   Proof of Theorem 3, p. 11 — pointwise value of problem (10)
-- statement:
--   Let $P$ be a finite poset, $C=[0,1]^P$ its unit cube, and $O(P)$ its order polytope. For every realization $\xi\in C$, the optimal value $q_P(\xi)$ of the second-stage program (10) is
--
--   $$
--   q_P(\xi)=\begin{cases}0,&\xi\in O(P),\\1,&\xi\notin O(P).\end{cases}
--   $$
--
--   This identifies the recourse value with the indicator of the cube outside the order polytope and supplies the pointwise step in Theorem 3.
--
--   **Formalization Note** The claim is restricted to the cube, which is the support of the paper's uniform law.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 11, proof of Theorem 3, first sentence. https://optimization-online.org/wp-content/uploads/2015/03/4825.pdf

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

namespace SPHardness.OrderPolytope

open Classical

/-- The value of (10) on the unit cube, as used in the proof of Theorem 3. -/
theorem secondStage_value (P : Type) [Fintype P] [PartialOrder P]
    (ξ : P → ℝ) (hξ : ξ ∈ cube P) :
    secondStageValue P ξ = if ξ ∈ orderPolytope P then 0 else 1 := by sorry

end SPHardness.OrderPolytope
