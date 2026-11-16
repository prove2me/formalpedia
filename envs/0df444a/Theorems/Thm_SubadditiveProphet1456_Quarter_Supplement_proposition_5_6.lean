-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_Supplement_proposition_5_6
-- name    : SubadditiveProphet1456.Quarter.Supplement.proposition_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:44:50.796625+00:00
-- url     : https://prove2.me/theorems/476c24d5-162b-4c82-8730-ecedcc2e596e
-- title:
--   Proposition 5.6 — Every cover of M costs at least m(1 − 3/e² + 2/e³ − 4/k^{1/4}); hence (23)
-- statement:
--   Let $k\ge2$, let $H=(U,M)$ be the complete $k$-uniform hypergraph on $k^2$ vertices with $m=\binom{k^2}{k}$ edges, and let $\beta=(e-1)^2/e^3$. The allowed pieces are the bulk pieces $E(H-J)$, $J\in\binom Uk$, of cost $\beta m$, and the singleton pieces $\{e\}$, $e\in M$, of cost $1$. Then:
--
--   1. every cover of $M$ by allowed pieces, given by a set $\mathcal J$ of bulk indices and a set $S$ of singleton edges with $M\subseteq\bigcup_{J\in\mathcal J}E(H-J)\cup S$, has cost
--   $$
--   |\mathcal J|\,\beta m+|S|\;\ge\;m\Big(1-\frac3{e^2}+\frac2{e^3}-\frac4{k^{1/4}}\Big);
--   $$
--   2. consequently the covering valuation $g$ of (33) satisfies the full-set bound (23):
--   $$
--   g(M)\ge m\Big(1-\frac3{e^2}+\frac2{e^3}-\frac4{k^{1/4}}\Big).
--   $$
--
--   The bound holds for covers with any number of bulk pieces, including none. It shows that the cheap bulk pieces still leave $g(M)$ large, which is what makes the ex-ante benchmark large in the impossibility instance.
--
--   Differences from the source:
--   - encoding: a cover of M by the allowed pieces → a pair (𝒥, S) of a finite set of bulk indices and a finite set of singleton edges whose pieces contain every edge, with cost |𝒥|βm + |S|; reason: a cover is a set of pieces labeled by their kind and index; covers listing a piece twice only cost more
--   - encoding: vertex set U with |U| = k², edges (U choose k) → U = Fin (k²), edges and k-vertex sets as the subtype of k-element Finsets; reason: relabeling, same instances
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.25, PDF p.26, Proposition 5.6; (23) printed p.19, PDF p.20; pieces and (33) printed pp.21–22, PDF pp.22–23.

import Definitions.Def_SubadditiveProphet1456_Quarter_Supplement_Hypergraph

open scoped BigOperators

namespace SubadditiveProphet1456.Quarter.Supplement

/-- STOC 2027 #1456, Proposition 5.6, printed p. 25 (PDF 26). A cover of `M = univ` is a set
`𝒥` of bulk indices (pieces `E(H − J)`, cost `βm`) and a set `S` of singleton edges (cost `1`);
the second clause is (23) for the covering valuation `g = coverValue k`. -/
theorem proposition_5_6 (k : ℕ) (hk : 2 ≤ k) :
    (∀ 𝒥 S : Finset (KSubset k), IsCover k Finset.univ 𝒥 S →
      (edgeCount k : ℝ) * (1 - 3 / Real.exp 1 ^ 2 + 2 / Real.exp 1 ^ 3 - 4 / (k : ℝ) ^ (1 / 4 : ℝ)) ≤
        coverCost k 𝒥 S) ∧
    (edgeCount k : ℝ) * (1 - 3 / Real.exp 1 ^ 2 + 2 / Real.exp 1 ^ 3 - 4 / (k : ℝ) ^ (1 / 4 : ℝ)) ≤
      coverValue k Finset.univ := by sorry

end SubadditiveProphet1456.Quarter.Supplement
