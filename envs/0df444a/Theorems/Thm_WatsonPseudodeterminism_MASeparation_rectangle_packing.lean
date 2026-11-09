-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_rectangle_packing
-- name    : WatsonPseudodeterminism.MASeparation.rectangle_packing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:36:10.934363+00:00
-- url     : https://prove2.me/theorems/25ac5efc-f34d-4ad3-937c-8969280466f9
-- title:
--   Lemma 3 ([GLMWZ16]) — Balanced subrectangle packing
-- statement:
--   Let $n,m\in\mathbb N$ satisfy $m\le n$, put $h=100\lceil\log_2n\rceil$, and let $R\subseteq S^m$ be a rectangle. For any real $k$ and output string $z$ with $|R_z|\ge2^{-k}|S^m_z|$, there is a finite family $\mathcal Q$ of pairwise disjoint subrectangles of $R$ such that
--
--   $$\sum_{Q\in\mathcal Q}|Q_z|\ge0.99|R_z|.$$
--
--   For each $Q\in\mathcal Q$ there is a structure $(a,b,c)$ of width $w$ satisfying
--
--   $$w\le k+8,\qquad z\text{ agrees with }c,\qquad Q\text{ is }(a,b,c)\text{-balanced},\qquad |Q_z|\ge2^{-(k+8-w)}|S^{a,b}_z|.$$
--
--   The structure may depend on $Q$. There is no added nonnegativity assumption on $k$ or asymptotic lower bound on $n$. This is the full packing statement as used in §4, including coverage, width, conditional balance, and density.
--
--   Differences from the source:
--   - reading: h = 100 log n → h = 100 * Nat.clog 2 n, with logarithms to base two; reason: block lengths are integral; rounding upward preserves the small-discrepancy regime specified in the brief
--   - encoding: rectangles and sets of pairwise disjoint subrectangles → finite pairs of sides and a Finset of such pairs, with disjoint Cartesian products; reason: the input spaces are finite; every rectangle is represented, including the empty rectangle
--   - encoding: a triple of blockwise totally assigned or unassigned partial assignments with width w → a consistent GadgetStructure whose width counts its assigned blocks; reason: whole-block options and a consistency field encode exactly the two source alternatives; w is derived rather than an unrelated parameter
--   - generalization: positive sizes for which the source logarithm is defined → all natural sizes, also allowing n = m = 0; reason: at zero coordinates the ambient space is a singleton; empty R is covered by the empty packing, and nonempty R forces k ≥ 0 and is covered by its width-zero structure
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), Lemma 3 ([GLMWZ16]), §2.2, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Structures

namespace WatsonPseudodeterminism.MASeparation

/-- Lemma 3 ([GLMWZ16]), p. 7. The structure is chosen separately for each Q;
k is real, and no sign or asymptotic restriction on k or n is imposed. -/
theorem rectangle_packing (n m : ℕ) (hm : m ≤ n)
    (R : GadgetRectangle (gadgetLength n) m) (z : Fin m → Bool) (k : ℝ)
    (hdensity : (2 : ℝ) ^ (-k) * ((slice (fullRectangle (gadgetLength n) m) z).card : ℝ) ≤
      ((slice R z).card : ℝ)) :
    ∃ qs : Finset (GadgetRectangle (gadgetLength n) m),
      (∀ Q ∈ qs, Subrectangle Q R) ∧
      (∀ Q ∈ qs, ∀ Q' ∈ qs, Q ≠ Q' → DisjointRectangles Q Q') ∧
      (0.99 : ℝ) * ((slice R z).card : ℝ) ≤ ∑ Q ∈ qs, ((slice Q z).card : ℝ) ∧
      ∀ Q ∈ qs, ∃ s : GadgetStructure (gadgetLength n) m,
        (s.width : ℝ) ≤ k + 8 ∧ s.Agrees z ∧ StructureBalanced Q s ∧
        (2 : ℝ) ^ (-(k + 8 - (s.width : ℝ))) * ((slice s.rectangle z).card : ℝ) ≤
          ((slice Q z).card : ℝ) := by sorry

end WatsonPseudodeterminism.MASeparation
