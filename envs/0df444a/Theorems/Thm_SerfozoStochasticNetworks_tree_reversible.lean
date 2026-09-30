-- Prove2me | Theorems.Thm_SerfozoStochasticNetworks_tree_reversible
-- name    : SerfozoStochasticNetworks.tree_reversible
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-19T02:51:30.392141+00:00
-- url     : https://prove2.me/theorems/d066274a-77c8-4184-8cff-b7d20e67c4f0
-- title:
--   Theorem 2.2 — a process whose communication graph is a tree is reversible
-- statement:
--   Let the state space be **finite**, let $q$ be a non-negative rate function with no self-loops
--   and with the two-way communication property, and let $\pi$ be a strictly positive invariant
--   measure of $q$. If the communication graph of $q$ — the simple graph joining distinct $x,y$
--   whenever either rate between them is non-zero — is a **tree**, then $\pi$ satisfies the detailed
--   balance equations.
--
--   So on a tree there is nothing to check: connectedness plus the absence of cycles forces
--   reversibility, and the equilibrium measure is the product of rate ratios along the unique path
--   from a fixed origin.
--
--   **Formalization Note** "Tree" is connected and acyclic, in the standard graph-theoretic sense.
--   The conclusion is detailed balance for the given $\pi$; since $\pi$ is positive, this also makes
--   the rate function reversible.
--
--   The state space is assumed finite. Serfozo assumes the process is ergodic, and the proof sums
--   the balance equations over one side of a cut; on an infinite state space that rearrangement
--   requires an integrability condition that "ergodic" leaves implicit. With finitely many states
--   the rearrangement is unconditional. The general case is not asserted here.
--
--   Absence of self-loops, $q(x,x)=0$, matches the convention for a jump process and keeps the
--   diagonal out of the cut argument; two-way communication is the standing assumption of the
--   chapter, and without it the conclusion is false — a directed cycle with all rates positive one
--   way and zero the other has a tree-free graph but is not reversible.
-- source:
--   Serfozo, Introduction to Stochastic Networks, Springer 1999, p. 46 (PDF p. 59), Theorem 2.2: "If the process X is ergodic and its communication graph is a tree, then X is reversible." Proof: "Let pi denote the stationary distribution of X. Recall that pi q(A, B) = sum_{x in A} sum_{y in B} pi(x) q(x, y) is the average rate of flow from A to B, and we noted in (1.2) that pi q(A, A^c) = ..." The communication graph is defined on the same page: "an undirected graph whose set of vertices is the state space E and there is an edge linking a pair x, y if either q(x, y) or q(y, x) is not 0." sha256 919f20ee082ec19faa80bdd923a5529fce9c4b6d3264fdb77c5efa64256bb463

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem tree_reversible {E : Type*} [Fintype E] (q : E → E → ℝ) (π : E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q) (hdiag : ∀ x, q x x = 0)
    (hπ : ∀ x, 0 < π x) (hinv : IsInvariant q π) (htree : (commGraph q).IsTree) :
    DetailedBalance q π := by sorry

end SerfozoStochasticNetworks
