-- Prove2me | Theorems.Thm_SignalSearch_Tree_lemma_2
-- name    : SignalSearch.Tree.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:53.851411+00:00
-- url     : https://prove2.me/theorems/6534c941-5969-49eb-a167-d9858536bc4e
-- title:
--   Lemma 2, p. 7 — the game G(Q, O, p) has a value, not larger than the total length μ of Q
-- statement:
--   Let $\tfrac12<p\le1$ and let $Q$ be a rooted tree with positive arc lengths and total length $\mu$. Then the search game $G(Q,O,p)$ has a value $V$, and
--   $$V\le\mu .$$
--
--   The bound says that signals cannot hurt the Searcher: without signals the value of the search game on a tree is $\mu$ (Gal, 1979). The proof of Theorem 7 uses it to sign the slopes of the payoff lines $T_{[1,1]}$ and $T_{[2,2]}$ (p. 11).
--
--   **Formalization Note.** "Has a value" is the existence of some $V$ with the published `IsGameValue`; the bound is stated for every such $V$.
--
--   Differences from the source:
--   - generalization: Q is a binary tree: every node has degree three or one, except possibly the root O (p. 5) → Q is any RTree, which also allows interior nodes of degree two and forks whose branches begin with a fork; reason: this is the paper's own conversion by arcs of length zero (p. 5); every binary tree with positive arc lengths is an RTree, so the statement specializes to the source's
--   - encoding: Q is a tree with arc lengths (a metric space) → every arc length is positive (PosLengths); reason: the arcs of a metric tree have positive length; Definition 4 and (3) divide by pμ1 + qμ2, which a zero-length branch would make undefined
--   - encoding: signals 1 or 2; the four Searcher choices [1,1], [2,2], [1,2] = follow, [2,1] = opposite → signals and branches are Bool (false = branch 1); an action is a map Bool → Bool, follow = id, opposite = not; reason: the same four strategies, labelled differently
--   - encoding: the payoff is the time T for the Searcher to reach the Hider, with random signals at the branch nodes → the payoff is the expected time, accumulated along the path to the leaf: each arc length once, plus twice the length of the other branch times the probability (from that node's signal, correct with probability p) of entering it first; reason: the time to reach a leaf depends only on the signals at the branch nodes of its path (p. 6) and is a sum over those nodes, so its expectation needs only each node's signal marginal; no joint law of the signals is assumed
--   - encoding: the value of the game and optimal strategies → the published matrix-game predicates IsGameValue, IsMinMaxStrategy, IsMaxMinStrategy (ZeroSumLP.DantzigExt.MatrixGame) on the finite game whose rows are leaves and whose columns are all pure Searcher strategies; reason: the game is a finite zero-sum game and these are its standard value and optimality notions
--   - reading: the title 'V < µ' and the sentence 'a value not larger than the total length µ' → V ≤ μ; reason: the strict reading is false for a single arc, where V = μ (p. 10 and the remark on p. 13); the sentence of the lemma says 'not larger than'
-- source:
--   Alpern, Lidbetter, Search for an Immobile Hider on a Binary Tree with Unreliable Locational Information, arXiv:2303.13378v2, p. 7, Lemma 2

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_SignalSearch_Tree_Model

namespace SignalSearch.Tree

/-- Lemma 2, p. 7: the game `G(Q, O, p)` has a value, and its value is not larger than the total
length `μ` of `Q`. -/
theorem lemma_2 (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (t : RTree) (ht : t.PosLengths) :
    (∃ V, IsValue p t V) ∧ ∀ V, IsValue p t V → V ≤ t.length := by sorry

end SignalSearch.Tree
