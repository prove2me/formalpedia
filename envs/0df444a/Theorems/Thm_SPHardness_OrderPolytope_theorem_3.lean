-- Prove2me | Theorems.Thm_SPHardness_OrderPolytope_theorem_3
-- name    : SPHardness.OrderPolytope.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:04.699148+00:00
-- url     : https://prove2.me/theorems/fb89418f-0273-4ee6-b069-d5e93a107e6c
-- title:
--   Theorem 3, p. 11 — accurate expected recourse values recover the linear-extension count
-- statement:
--   This states the correctness of the counting reduction underlying Theorem 3. Let $P$ be a finite poset with $k=|P|$. Let $Q(P)$ be the expected optimal value of the random-recourse program (10) under the uniform law on $[0,1]^P$, and let $N(P)$ count its linear extensions. If $\vartheta$ approximates $Q(P)$ to absolute accuracy $\varepsilon$ with $0\le\varepsilon<1/(2k!)$, then
--
--   $$
--   \left|k!(1-\vartheta)-N(P)\right|<\frac12.
--   $$
--
--   Thus $N(P)$ is the unique nearest integer to $k!(1-\vartheta)$. The result combines the pointwise value of (10), the expected-value/volume identity, and the factorial volume identity.
--
--   **Formalization Note** The original Theorem 3 asserts strong #P-hardness. This statement formalizes the mathematical correctness of its reduction, not a complexity class, polynomial-time computability, input bit lengths, or the unary-encoding argument. A general finite poset represents the paper's $S=\{1,\ldots,k\}$ with its given partial order; $k$ is its cardinality, not an independent parameter.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 11, Theorem 3 and proof; pp. 10–11, Lemma 3. https://optimization-online.org/wp-content/uploads/2015/03/4825.pdf

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

namespace SPHardness.OrderPolytope

open scoped Nat

/-- Correctness of the counting reduction underlying Theorem 3. -/
theorem theorem_3 (P : Type) [Fintype P] [PartialOrder P]
    (ϑ ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / (2 * ((Fintype.card P)! : ℝ)))
    (hϑ : |ϑ - expRecourse P| ≤ ε) :
    |((Fintype.card P)! : ℝ) * (1 - ϑ) - numLinExt P| < 1 / 2 := by sorry

end SPHardness.OrderPolytope
