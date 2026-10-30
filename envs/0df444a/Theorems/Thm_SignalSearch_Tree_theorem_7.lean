-- Prove2me | Theorems.Thm_SignalSearch_Tree_theorem_7
-- name    : SignalSearch.Tree.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:11.852001+00:00
-- url     : https://prove2.me/theorems/75744438-bd6d-4f94-b573-bfb41fc13662
-- title:
--   Theorem 7, pp. 9–10 — the value is 2qμ + (p − q)D_Q; λ̄ is optimal for the Hider; the favoring-bias strategy β is optimal for the Searcher
-- statement:
--   Let $\tfrac12<p\le1$, $q=1-p$, and let $(Q,O)$ be a rooted tree with positive arc lengths and total length $\mu=\mu(Q)$. Let $D_Q$ be its mean depth with respect to the Hider distribution $\bar\lambda$ of Definition 4.
--
--   1. The value $V=V(Q)$ of the game $G(Q,O,p)$ is
--   $$V(Q)=2q\mu+(p-q)D_Q. \tag{2}$$
--   2. The hiding distribution $\bar\lambda$ is optimal for the Hider: it guarantees an expected search time of at least $V(Q)$ against every pure Searcher strategy.
--   3. At every branch node with branches $Q_1$ and $Q_2$ of lengths $\mu_1$ and $\mu_2$, where $Q_1$ denotes the favored branch, let the Searcher search the favored branch first with probability
--   $$\beta=\frac{(p-q)(D_{Q_1}-D_{Q_2})}{2(p\mu_1+q\mu_2)} \tag{3}$$
--   and with the complementary probability $1-\beta$ follow the signal, whichever direction it points. This Searcher strategy is optimal: it reaches every leaf in expected time at most $V(Q)$.
--
--   The theorem solves the search game with unreliable signals on every tree in closed form. As $p\to\tfrac12$ it recovers Gal's value $\mu$ for the game without signals, and at $p=1$ the value is the mean depth $D_Q$, now concentrated on the deepest leaves.
--
--   **Formalization Note.** (i) is `IsValue`, the published `IsGameValue` of the payoff matrix; (ii) and (iii) are the published `IsMaxMinStrategy` and `IsMinMaxStrategy` with the value (2): each strategy is a probability vector that guarantees (2), and no strategy of the same player guarantees better. The Searcher strategy of (iii) is `favoringStrategy`, the product over all branch nodes of each node's law ($\beta$ on "favored branch first", $1-\beta$ on "follow"); the Hider's guarantee in (ii) holds against every pure strategy, not only against strategies of this form.
--
--   Differences from the source:
--   - generalization: Q is a binary tree: every node has degree three or one, except possibly the root O (p. 5) → Q is any RTree, which also allows interior nodes of degree two and forks whose branches begin with a fork; reason: this is the paper's own conversion by arcs of length zero (p. 5); every binary tree with positive arc lengths is an RTree, so the statement specializes to the source's
--   - encoding: Q is a tree with arc lengths (a metric space) → every arc length is positive (PosLengths); reason: the arcs of a metric tree have positive length; Definition 4 and (3) divide by pμ1 + qμ2, which a zero-length branch would make undefined
--   - encoding: signals 1 or 2; the four Searcher choices [1,1], [2,2], [1,2] = follow, [2,1] = opposite → signals and branches are Bool (false = branch 1); an action is a map Bool → Bool, follow = id, opposite = not; reason: the same four strategies, labelled differently
--   - encoding: the payoff is the time T for the Searcher to reach the Hider, with random signals at the branch nodes → the payoff is the expected time, accumulated along the path to the leaf: each arc length once, plus twice the length of the other branch times the probability (from that node's signal, correct with probability p) of entering it first; reason: the time to reach a leaf depends only on the signals at the branch nodes of its path (p. 6) and is a sum over those nodes, so its expectation needs only each node's signal marginal; no joint law of the signals is assumed
--   - encoding: the value of the game and optimal strategies → the published matrix-game predicates IsGameValue, IsMinMaxStrategy, IsMaxMinStrategy (ZeroSumLP.DantzigExt.MatrixGame) on the finite game whose rows are leaves and whose columns are all pure Searcher strategies; reason: the game is a finite zero-sum game and these are its standard value and optimality notions
--   - encoding: without loss of generality D(Q1) ≥ D(Q2), and Q1 is the favored branch → branch 1 of fork t₁ t₂ is favored iff D(t₂) ≤ D(t₁); a tie goes to branch 1; reason: the page does not say which branch is favored on a tie; there β = 0, and the theorem holds for either choice of the weights of (1)
--   - reading: (iii) 'when at a branch node … it is optimal for the Searcher to search the favored branch first with probability β' → the strategy uses at every branch node of the tree the β computed from that node's own two branches; reason: the description of the Searcher's solution on p. 6 says 'at every branch node j'; the proof applies (3) at each node of the induction
--   - encoding: a behavioural strategy: an independent random choice at each branch node → the mixed strategy on pure strategies that is the product over branch nodes of each node's law; reason: a behavioural strategy on a tree corresponds to this product mixed strategy, with the same expected time at every leaf
-- source:
--   Alpern, Lidbetter, Search for an Immobile Hider on a Binary Tree with Unreliable Locational Information, arXiv:2303.13378v2, pp. 9–10, Theorem 7, eqs. (2) and (3)

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_SignalSearch_Tree_Model

namespace SignalSearch.Tree

open ZeroSumLP.DantzigExt

/-- Theorem 7, pp. 9–10. For every rooted tree `Q` with positive arc lengths and `1/2 < p ≤ 1`,
`q = 1 − p`:
(i) the value of `G(Q, O, p)` is `V(Q) = 2qμ + (p − q)D_Q` (2);
(ii) the hiding distribution `λ̄` is optimal for the Hider (a max-min strategy with value `V(Q)`);
(iii) the Searcher strategy that at every branch node searches the favored branch first with
probability `β` of (3) and otherwise follows the signal is optimal (a min-max strategy with value
`V(Q)`). -/
theorem theorem_7 (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t : RTree) (ht : t.PosLengths) :
    IsValue p t (2 * (1 - p) * t.length + (p - (1 - p)) * meanDepth p t) ∧
    IsMaxMinStrategy (payoff p t) (hiderDist p t)
      (2 * (1 - p) * t.length + (p - (1 - p)) * meanDepth p t) ∧
    IsMinMaxStrategy (payoff p t) (favoringStrategy p t)
      (2 * (1 - p) * t.length + (p - (1 - p)) * meanDepth p t) := by sorry

end SignalSearch.Tree
