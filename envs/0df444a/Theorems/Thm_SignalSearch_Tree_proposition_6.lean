-- Prove2me | Theorems.Thm_SignalSearch_Tree_proposition_6
-- name    : SignalSearch.Tree.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:44.170433+00:00
-- url     : https://prove2.me/theorems/37f0567c-5eed-4178-8d88-9fbb9c02c960
-- title:
--   Proposition 6, p. 8 — D_Q = ℓ + D_{Q′} at a degree-one root; D_Q = (pμ1D_{Q1} + qμ2D_{Q2})/(pμ1 + qμ2) at a branch root, Q1 favored
-- statement:
--   Let $\tfrac12<p\le1$, $q=1-p$, and let all arcs have positive length. Write $D_Q$ for the mean depth of $Q$ with respect to the Hider distribution $\bar\lambda$.
--
--   1. If the root $O$ has degree one, with an arc $OA$ of length $\ell$ and subtree $Q'$ rooted at $A$, then
--   $$D_Q=\ell+D_{Q'}.$$
--   2. If $O$ is a branch node with branches $Q_1,Q_2$ of lengths $\mu_1,\mu_2$ and $Q_1$ is favored, $D_{Q_1}\ge D_{Q_2}$, then
--   $$D_Q=\frac{p\mu_1D_{Q_1}+q\mu_2D_{Q_2}}{p\mu_1+q\mu_2}.$$
--   3. Symmetrically, if $D_{Q_2}\ge D_{Q_1}$, then $D_Q=\dfrac{p\mu_2D_{Q_2}+q\mu_1D_{Q_1}}{p\mu_2+q\mu_1}$.
--
--   The proposition expresses the mean depth of Definition 3, a sum over all leaves, recursively; it is the identity the proof of Theorem 7 uses to pass formula (2) through a degree-one root and through a branch root.
--
--   **Formalization Note.** $D_Q$ is `meanDepth p t`, the sum $\sum_v\bar\lambda(v)d(O,v)$ of Definition 3, not a recursion. Item 3 is the paper's "without loss of generality $Q_1$ is favored" for the other orientation of the fork.
--
--   Differences from the source:
--   - generalization: Q is a binary tree: every node has degree three or one, except possibly the root O (p. 5) → Q is any RTree, which also allows interior nodes of degree two and forks whose branches begin with a fork; reason: this is the paper's own conversion by arcs of length zero (p. 5); every binary tree with positive arc lengths is an RTree, so the statement specializes to the source's
--   - encoding: Q is a tree with arc lengths (a metric space) → every arc length is positive (PosLengths); reason: the arcs of a metric tree have positive length; Definition 4 and (3) divide by pμ1 + qμ2, which a zero-length branch would make undefined
--   - encoding: without loss of generality D(Q1) ≥ D(Q2), and Q1 is the favored branch → branch 1 of fork t₁ t₂ is favored iff D(t₂) ≤ D(t₁); a tie goes to branch 1; reason: the page does not say which branch is favored on a tie; there β = 0, and the theorem holds for either choice of the weights of (1)
--   - encoding: without loss of generality Q1 is the favored branch → two clauses, one for each branch of fork t₁ t₂ having the larger (or equal) mean depth; reason: the branches of an RTree fork are labelled, so the WLOG is stated for both labels
--   - reading: D_Q = ℓ + D′_Q → meanDepth (cons ℓ t) = ℓ + meanDepth t, i.e. D_Q = ℓ + D_{Q′}; reason: the proof on p. 9 defines D′_Q as the mean depth of Q′ with the distances measured from A
-- source:
--   Alpern, Lidbetter, Search for an Immobile Hider on a Binary Tree with Unreliable Locational Information, arXiv:2303.13378v2, p. 8, Proposition 6

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_SignalSearch_Tree_Model

namespace SignalSearch.Tree

/-- Proposition 6, p. 8. If the root has degree one, with an arc of length `ℓ` to the subtree `Q′`,
then `D_Q = ℓ + D_{Q′}`. If the root is a branch node with branches `Q₁ = t₁`, `Q₂ = t₂` of lengths
`μ₁, μ₂`, then `D_Q = (p μ_f D_{Q_f} + q μ_u D_{Q_u}) / (p μ_f + q μ_u)` where `f` is a branch of
greater or equal mean depth and `u` the other one (the paper's "without loss of generality `Q₁` is
favored", stated for both orientations). -/
theorem proposition_6 (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    (∀ (ℓ : ℝ) (t : RTree), 0 < ℓ → t.PosLengths →
      meanDepth p (.cons ℓ t) = ℓ + meanDepth p t) ∧
    (∀ t₁ t₂ : RTree, t₁.PosLengths → t₂.PosLengths → meanDepth p t₂ ≤ meanDepth p t₁ →
      meanDepth p (.fork t₁ t₂) =
        (p * t₁.length * meanDepth p t₁ + (1 - p) * t₂.length * meanDepth p t₂) /
          (p * t₁.length + (1 - p) * t₂.length)) ∧
    (∀ t₁ t₂ : RTree, t₁.PosLengths → t₂.PosLengths → meanDepth p t₁ ≤ meanDepth p t₂ →
      meanDepth p (.fork t₁ t₂) =
        (p * t₂.length * meanDepth p t₂ + (1 - p) * t₁.length * meanDepth p t₁) /
          (p * t₂.length + (1 - p) * t₁.length)) := by sorry

end SignalSearch.Tree
