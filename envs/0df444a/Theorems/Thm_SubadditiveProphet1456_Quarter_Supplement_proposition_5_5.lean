-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_Supplement_proposition_5_5
-- name    : SubadditiveProphet1456.Quarter.Supplement.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:44:22.707957+00:00
-- url     : https://prove2.me/theorems/a3f28c45-4c94-422f-9653-f50e018cc4fa
-- title:
--   Proposition 5.5 — Uncovered edges after q bulk pieces, at least (1 − 1/e)^q − 4/k^{1/4}
-- statement:
--   Let $k\ge2$, let $H=(U,M)$ be the complete $k$-uniform hypergraph on $k^2$ vertices with $m=\binom{k^2}{k}$ edges, and for $J\subseteq U$ let $E(H-J)$ be the set of edges avoiding $J$. For every integer $q\ge1$ and every $J_1,\ldots,J_q\in\binom Uk$, overlapping or repeated sets included,
--   $$
--   \frac1m\Big|M\setminus\bigcup_{\ell=1}^{q}E(H-J_\ell)\Big|\;\ge\;(1-e^{-1})^q-\frac{4}{k^{1/4}}. \tag{39}
--   $$
--   The error depends only on $k$; it is uniform over $q$ and the vertex sets.
--
--   An edge escapes all $q$ bulk pieces exactly when it meets every $J_\ell$, so (39) lower-bounds the number of edges that a cover with $q$ bulk pieces must still pay for with singletons. It is the counting estimate behind Proposition 5.6.
--
--   Differences from the source:
--   - encoding: J_1, …, J_q ∈ (U choose k) → a function J : Fin q → k-subsets of Fin (k²), indices 0, …, q − 1; reason: an arbitrary function allows repetitions and overlaps, as the source does
--   - encoding: vertex set U with |U| = k², edges (U choose k) → U = Fin (k²), edges as the subtype of k-element Finsets; reason: relabeling, same instances
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.25, PDF p.26, Proposition 5.5, display (39).

import Definitions.Def_SubadditiveProphet1456_Quarter_Supplement_Hypergraph

open scoped BigOperators

namespace SubadditiveProphet1456.Quarter.Supplement

/-- STOC 2027 #1456, Proposition 5.5, printed p. 25 (PDF 26), display (39). The vertex sets
`J ℓ`, `ℓ < q`, may overlap or repeat. -/
theorem proposition_5_5 (k : ℕ) (hk : 2 ≤ k) (q : ℕ) (hq : 1 ≤ q) (J : Fin q → KSubset k) :
    (1 - Real.exp (-1)) ^ q - 4 / (k : ℝ) ^ (1 / 4 : ℝ) ≤
      (1 / (edgeCount k : ℝ)) *
        ((Finset.univ \ Finset.univ.biUnion fun ℓ => avoidEdges k (J ℓ).1).card : ℝ) := by sorry

end SubadditiveProphet1456.Quarter.Supplement
