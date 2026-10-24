-- Prove2me | Theorems.Thm_SignalSearch_Tree_theorem_7_follow_dominates
-- name    : SignalSearch.Tree.theorem_7_follow_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:57.094757+00:00
-- url     : https://prove2.me/theorems/53c23551-be42-455d-8ed9-2a0b90b1028f
-- title:
--   Proof of Theorem 7, pp. 10–11 — “opposite” is dominated by “follow”: the columns differ by (2μ2(2p − 1), 2μ1(2p − 1))
-- statement:
--   Let $\tfrac12<p\le1$, $q=1-p$, and let $Q$ have a branch root with branches $Q_1,Q_2$ of lengths $\mu_1,\mu_2$, all arcs of positive length.
--
--   1. In Table 1 (for any $V_1,V_2$), the "opposite" column minus the "follow" column is
--   $$\begin{pmatrix}p\cdot2\mu_2+V_1\\ p\cdot2\mu_1+V_2\end{pmatrix}-\begin{pmatrix}q\cdot2\mu_2+V_1\\ q\cdot2\mu_1+V_2\end{pmatrix}=\begin{pmatrix}2\mu_2(2p-1)\\ 2\mu_1(2p-1)\end{pmatrix}.$$
--   2. In the game on the tree, take any pure Searcher strategy $s$ and compare the strategy that uses "opposite" at the root with the one that uses "follow" there, all other choices of $s$ unchanged. For every leaf $v$ of $Q_1$ the expected time to reach $v$ increases by exactly $2\mu_2(2p-1)$, and for every leaf of $Q_2$ by exactly $2\mu_1(2p-1)$.
--   3. In particular, since $p>\tfrac12$, "follow" reaches every leaf strictly faster in expectation than "opposite": "opposite" is dominated by "follow".
--
--   This removes the fourth column from the analysis of the Table 1 game in the proof of Theorem 7.
--
--   **Formalization Note.** "Follow" is the action `id` and "opposite" is `not`; the modified strategies are `Function.update s (root) id` and `Function.update s (root) not`.
--
--   Differences from the source:
--   - generalization: Q is a binary tree: every node has degree three or one, except possibly the root O (p. 5) → Q is any RTree, which also allows interior nodes of degree two and forks whose branches begin with a fork; reason: this is the paper's own conversion by arcs of length zero (p. 5); every binary tree with positive arc lengths is an RTree, so the statement specializes to the source's
--   - encoding: Q is a tree with arc lengths (a metric space) → every arc length is positive (PosLengths); reason: the arcs of a metric tree have positive length; Definition 4 and (3) divide by pμ1 + qμ2, which a zero-length branch would make undefined
--   - encoding: signals 1 or 2; the four Searcher choices [1,1], [2,2], [1,2] = follow, [2,1] = opposite → signals and branches are Bool (false = branch 1); an action is a map Bool → Bool, follow = id, opposite = not; reason: the same four strategies, labelled differently
--   - encoding: the payoff is the time T for the Searcher to reach the Hider, with random signals at the branch nodes → the payoff is the expected time, accumulated along the path to the leaf: each arc length once, plus twice the length of the other branch times the probability (from that node's signal, correct with probability p) of entering it first; reason: the time to reach a leaf depends only on the signals at the branch nodes of its path (p. 6) and is a sum over those nodes, so its expectation needs only each node's signal marginal; no joint law of the signals is assumed
--   - generalization: the comparison of the last two columns of Table 1 → the column comparison of Table 1, and in addition the same comparison in the game on the tree, for every pure strategy and every leaf; reason: the Table 1 clause is the page's computation; the tree clauses are the pointwise statement whose averages are the Table 1 entries
-- source:
--   Alpern, Lidbetter, Search for an Immobile Hider on a Binary Tree with Unreliable Locational Information, arXiv:2303.13378v2, pp. 10–11, proof of Theorem 7, 'We now show that "follow" dominates "opposite" for any p > 1/2 …'

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_SignalSearch_Tree_Model

namespace SignalSearch.Tree

/-- Proof of Theorem 7, p. 11: "follow" dominates "opposite". In Table 1 the "opposite" column
exceeds the "follow" column by `(2μ₂(2p − 1), 2μ₁(2p − 1))`; in the game on the tree, replacing
"follow" by "opposite" at the root of `fork t₁ t₂`, with everything else in the pure strategy `s`
unchanged, increases the expected time to every leaf by `2μ(other branch)(2p − 1) > 0`. -/
theorem theorem_7_follow_dominates (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t₁ t₂ : RTree)
    (ht₁ : t₁.PosLengths) (ht₂ : t₂.PosLengths) :
    (∀ V₁ V₂ : ℝ,
      table1 p t₁.length t₂.length V₁ V₂ false not -
          table1 p t₁.length t₂.length V₁ V₂ false id = 2 * t₂.length * (2 * p - 1) ∧
        table1 p t₁.length t₂.length V₁ V₂ true not -
          table1 p t₁.length t₂.length V₁ V₂ true id = 2 * t₁.length * (2 * p - 1)) ∧
    (∀ (s : SPure (.fork t₁ t₂)) (v : Leaf t₁),
      time p (.fork t₁ t₂) (Function.update s (.root t₁ t₂) not) (.left t₂ v) =
        time p (.fork t₁ t₂) (Function.update s (.root t₁ t₂) id) (.left t₂ v) +
          2 * t₂.length * (2 * p - 1)) ∧
    (∀ (s : SPure (.fork t₁ t₂)) (v : Leaf t₂),
      time p (.fork t₁ t₂) (Function.update s (.root t₁ t₂) not) (.right t₁ v) =
        time p (.fork t₁ t₂) (Function.update s (.root t₁ t₂) id) (.right t₁ v) +
          2 * t₁.length * (2 * p - 1)) ∧
    (∀ (s : SPure (.fork t₁ t₂)) (v : Leaf (.fork t₁ t₂)),
      time p (.fork t₁ t₂) (Function.update s (.root t₁ t₂) id) v <
        time p (.fork t₁ t₂) (Function.update s (.root t₁ t₂) not) v) := by sorry

end SignalSearch.Tree
