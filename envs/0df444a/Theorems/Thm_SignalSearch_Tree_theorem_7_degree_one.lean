-- Prove2me | Theorems.Thm_SignalSearch_Tree_theorem_7_degree_one
-- name    : SignalSearch.Tree.theorem_7_degree_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:45.488307+00:00
-- url     : https://prove2.me/theorems/18dcf41a-07bd-416c-948d-7fef4b4e5129
-- title:
--   Proof of Theorem 7, p. 10 — at a root of degree one with arc OA of length ℓ, V(Q) = ℓ + V(Q′)
-- statement:
--   Let $\tfrac12<p\le1$. Let $Q$ be a rooted tree whose root $O$ has degree one: an arc $OA$ of length $\ell>0$ leads to the subtree $Q'$ rooted at $A$, all of whose arcs have positive length. Then the value of the search game on $Q$ is the value on $Q'$ plus $\ell$:
--   $$V(Q)=\ell+V(Q').$$
--   Precisely, for every real $V'$, $V'$ is the value of $G(Q',A,p)$ if and only if $\ell+V'$ is the value of $G(Q,O,p)$.
--
--   This is the degree-one step of the induction that proves Theorem 7: together with Proposition 6 it shows that formula (2) passes from $Q'$ to $Q$.
--
--   **Formalization Note.** $Q$ is `RTree.cons ℓ t` with $Q'=$ `t`; the value is the published `IsGameValue` of the payoff matrix.
--
--   Differences from the source:
--   - generalization: Q is a binary tree: every node has degree three or one, except possibly the root O (p. 5) → Q is any RTree, which also allows interior nodes of degree two and forks whose branches begin with a fork; reason: this is the paper's own conversion by arcs of length zero (p. 5); every binary tree with positive arc lengths is an RTree, so the statement specializes to the source's
--   - encoding: Q is a tree with arc lengths (a metric space) → every arc length is positive (PosLengths); reason: the arcs of a metric tree have positive length; Definition 4 and (3) divide by pμ1 + qμ2, which a zero-length branch would make undefined
--   - encoding: signals 1 or 2; the four Searcher choices [1,1], [2,2], [1,2] = follow, [2,1] = opposite → signals and branches are Bool (false = branch 1); an action is a map Bool → Bool, follow = id, opposite = not; reason: the same four strategies, labelled differently
--   - encoding: the payoff is the time T for the Searcher to reach the Hider, with random signals at the branch nodes → the payoff is the expected time, accumulated along the path to the leaf: each arc length once, plus twice the length of the other branch times the probability (from that node's signal, correct with probability p) of entering it first; reason: the time to reach a leaf depends only on the signals at the branch nodes of its path (p. 6) and is a sum over those nodes, so its expectation needs only each node's signal marginal; no joint law of the signals is assumed
--   - encoding: the value of the game and optimal strategies → the published matrix-game predicates IsGameValue, IsMinMaxStrategy, IsMaxMinStrategy (ZeroSumLP.DantzigExt.MatrixGame) on the finite game whose rows are leaves and whose columns are all pure Searcher strategies; reason: the game is a finite zero-sum game and these are its standard value and optimality notions
--   - encoding: V(Q) = ℓ + V(Q′), an equation between the two values → for every V′: V′ is the value on Q′ iff ℓ + V′ is the value on Q; reason: the value of a finite zero-sum game is unique, so the equation and the equivalence say the same
-- source:
--   Alpern, Lidbetter, Search for an Immobile Hider on a Binary Tree with Unreliable Locational Information, arXiv:2303.13378v2, p. 10, proof of Theorem 7, 'Then it is easy to see that V(Q) = ℓ + V(Q′)'

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_SignalSearch_Tree_Model

namespace SignalSearch.Tree

/-- Proof of Theorem 7, p. 10: if the root `O` has degree one, with an arc `OA` of length `ℓ`
leading to the subtree `Q′` rooted at `A`, then `V(Q) = ℓ + V(Q′)`: a number `V′` is the value of
`G(Q′, A, p)` exactly when `ℓ + V′` is the value of `G(Q, O, p)`. -/
theorem theorem_7_degree_one (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (t : RTree) (ht : t.PosLengths) (V' : ℝ) :
    IsValue p t V' ↔ IsValue p (.cons ℓ t) (ℓ + V') := by sorry

end SignalSearch.Tree
