-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_Supplement_proposition_5_4
-- name    : SubadditiveProphet1456.Quarter.Supplement.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:43:48.738744+00:00
-- url     : https://prove2.me/theorems/ebe236a0-132e-4298-8f39-d174e0ad5f0e
-- title:
--   Proposition 5.4 — Coupling the independent p-sample with a uniform edge, Pr[X ⊈ e] ≤ k^{-1/2}
-- statement:
--   Let $k\ge2$ and $U=\{0,\ldots,k^2-1\}$. Let $X\subseteq U$ contain each vertex independently with probability
--   $$
--   p=\frac{1-k^{-1/4}}{k},
--   $$
--   so that $\Pr[X=A]=p^{|A|}(1-p)^{k^2-|A|}$, and let $e$ be a uniformly random $k$-subset of $U$, i.e. a uniformly random edge of the complete $k$-uniform hypergraph, of probability $1/m$ each, $m=\binom{k^2}{k}$. Then:
--
--   1. there is a coupling of $X$ and $e$ (a nonnegative joint mass function with exactly these two marginals) under which
--   $$
--   \Pr[X\not\subseteq e]\le k^{-1/2};
--   $$
--   2. for every increasing family $\mathcal F$ of subsets of $U$ (that is, $A\in\mathcal F$ and $A\subseteq B\subseteq U$ imply $B\in\mathcal F$),
--   $$
--   \Pr[e\in\mathcal F]\ge\Pr[X\in\mathcal F]-k^{-1/2}. \tag{36}
--   $$
--
--   This comparison transfers lower bounds for the product measure, where correlation inequalities apply, to the uniform edge, and is used in the proof of Proposition 5.5.
--
--   Differences from the source:
--   - encoding: random set X, uniformly random edge e and a coupling of the two → a nonnegative joint mass function on (subsets of U) × (k-subsets of U) with first marginal p^{|A|}(1 − p)^{k² − |A|} and second marginal 1/m; probabilities are sums of masses; reason: on finite spaces a coupling is exactly a joint mass function with the given marginals
--   - encoding: increasing family F ⊆ 2^U → IsUpperSet F for a set F of Finsets of Fin (k²) ordered by inclusion; reason: same notion
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.24, PDF p.25, Proposition 5.4, display (36).

import Definitions.Def_SubadditiveProphet1456_Quarter_Supplement_Hypergraph

open scoped BigOperators

namespace SubadditiveProphet1456.Quarter.Supplement

/-- STOC 2027 #1456, Proposition 5.4, printed p. 24 (PDF 25). `X ⊆ U` contains each vertex
independently with probability `p = (1 − k^{−1/4})/k`; `e` is uniform on `(U choose k)`.
The coupling is a joint mass function with exactly these two marginals. -/
theorem proposition_5_4 (k : ℕ) (hk : 2 ≤ k) :
    (∃ μ : Finset (Vertex k) × KSubset k → ℝ, IsSampleCoupling k μ ∧
      notSubsetMass k μ ≤ (k : ℝ) ^ (-(1 / 2 : ℝ))) ∧
    ∀ F : Set (Finset (Vertex k)), IsUpperSet F →
      sampleEventProb k F - (k : ℝ) ^ (-(1 / 2 : ℝ)) ≤ uniformEventProb k F := by sorry

end SubadditiveProphet1456.Quarter.Supplement
