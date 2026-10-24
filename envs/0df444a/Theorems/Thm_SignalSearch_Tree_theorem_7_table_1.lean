-- Prove2me | Theorems.Thm_SignalSearch_Tree_theorem_7_table_1
-- name    : SignalSearch.Tree.theorem_7_table_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:54.265232+00:00
-- url     : https://prove2.me/theorems/8cb89947-5f23-4761-b035-81c487e60d0f
-- title:
--   Proof of Theorem 7, pp. 10–11 — at a branch root the game has the value of the 2 × 4 matrix game of Table 1
-- statement:
--   Let $\tfrac12<p\le1$, $q=1-p$. Let $Q$ have a branch root $O$ with branches $Q_1,Q_2$ of lengths $\mu_1,\mu_2$, all arcs of positive length, and let $V_1,V_2$ be the values of the games $G(Q_1,O,p)$ and $G(Q_2,O,p)$. Let $M$ be the $2\times 4$ matrix of Table 1, rows the Hider's branch and columns the Searcher's choices $[X,Y]$ (the branch searched first on signal 1 and on signal 2):
--   $$\begin{array}{c|cccc} & [1,1] & [2,2] & [1,2]=\text{follow} & [2,1]=\text{opposite}\\\hline 1 & V_1 & 2\mu_2+V_1 & q\cdot2\mu_2+V_1 & p\cdot2\mu_2+V_1\\ 2 & 2\mu_1+V_2 & V_2 & q\cdot2\mu_1+V_2 & p\cdot2\mu_1+V_2\end{array}$$
--   Then for every real $V$: $V$ is the value of $G(Q,O,p)$ if and only if $V$ is the value of the matrix game $M$ (Hider maximizing over rows, Searcher minimizing over columns).
--
--   This reduction is the branch-node step of the proof of Theorem 7: it replaces the game on the whole tree by a $2\times4$ game whose entries involve only the lengths and the values of the two branches.
--
--   **Formalization Note.** $M$ is `table1 p μ₁ μ₂ V₁ V₂`, whose columns are indexed by the actions `Bool → Bool`; row `false` is branch 1.
--
--   Differences from the source:
--   - generalization: Q is a binary tree: every node has degree three or one, except possibly the root O (p. 5) → Q is any RTree, which also allows interior nodes of degree two and forks whose branches begin with a fork; reason: this is the paper's own conversion by arcs of length zero (p. 5); every binary tree with positive arc lengths is an RTree, so the statement specializes to the source's
--   - encoding: Q is a tree with arc lengths (a metric space) → every arc length is positive (PosLengths); reason: the arcs of a metric tree have positive length; Definition 4 and (3) divide by pμ1 + qμ2, which a zero-length branch would make undefined
--   - encoding: signals 1 or 2; the four Searcher choices [1,1], [2,2], [1,2] = follow, [2,1] = opposite → signals and branches are Bool (false = branch 1); an action is a map Bool → Bool, follow = id, opposite = not; reason: the same four strategies, labelled differently
--   - encoding: the payoff is the time T for the Searcher to reach the Hider, with random signals at the branch nodes → the payoff is the expected time, accumulated along the path to the leaf: each arc length once, plus twice the length of the other branch times the probability (from that node's signal, correct with probability p) of entering it first; reason: the time to reach a leaf depends only on the signals at the branch nodes of its path (p. 6) and is a sum over those nodes, so its expectation needs only each node's signal marginal; no joint law of the signals is assumed
--   - encoding: the value of the game and optimal strategies → the published matrix-game predicates IsGameValue, IsMinMaxStrategy, IsMaxMinStrategy (ZeroSumLP.DantzigExt.MatrixGame) on the finite game whose rows are leaves and whose columns are all pure Searcher strategies; reason: the game is a finite zero-sum game and these are its standard value and optimality notions
--   - reading: the resulting matrix game is given by Table 1, where V1 and V2 are the values of the games on Q1 and Q2 → for every V, V is the value of the game on the tree iff V is the value of the Table 1 game; reason: the tree game has far more pure strategies than Table 1 has columns, so 'is given by' cannot mean equality of matrices; the paper uses it only to compute the value
-- source:
--   Alpern, Lidbetter, Search for an Immobile Hider on a Binary Tree with Unreliable Locational Information, arXiv:2303.13378v2, pp. 10–11, proof of Theorem 7, 'It is easy to see that the resulting matrix game is given by Table 1', Table 1 (p. 11)

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_SignalSearch_Tree_Model

namespace SignalSearch.Tree

open ZeroSumLP.DantzigExt

/-- Proof of Theorem 7, pp. 10–11: at a branch root with branches `Q₁ = t₁`, `Q₂ = t₂` whose games
have values `V₁`, `V₂`, the game `G(Q, O, p)` has the same value as the 2 × 4 matrix game of
Table 1. -/
theorem theorem_7_table_1 (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t₁ t₂ : RTree)
    (ht₁ : t₁.PosLengths) (ht₂ : t₂.PosLengths) (V₁ V₂ : ℝ)
    (hV₁ : IsValue p t₁ V₁) (hV₂ : IsValue p t₂ V₂) (V : ℝ) :
    IsValue p (.fork t₁ t₂) V ↔ IsGameValue (table1 p t₁.length t₂.length V₁ V₂) V := by sorry

end SignalSearch.Tree
