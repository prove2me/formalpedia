-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_Supplement_proposition_5_3
-- name    : SubadditiveProphet1456.Quarter.Supplement.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:43:12.309642+00:00
-- url     : https://prove2.me/theorems/5388874e-19fa-4d57-93f7-aa2045d974bf
-- title:
--   Proposition 5.3 — The covering valuation is normalised, monotone, subadditive and satisfies the residual bound
-- statement:
--   Let $k\ge2$, let $H=(U,M)$ be the complete $k$-uniform hypergraph on $|U|=k^2$ vertices with $m=|M|=\binom{k^2}{k}$ edges, let $\beta=(e-1)^2/e^3$, and let $g$ be the covering valuation (33): $g(S)$ is the minimum of $|\mathcal J|\beta m+|S\setminus\bigcup_{J\in\mathcal J}E(H-J)|$ over finite families $\mathcal J$ of $k$-vertex sets. Then
--
--   1. $g(\varnothing)=0$;
--   2. $g(S)\le g(T)$ whenever $S\subseteq T\subseteq M$;
--   3. $g(S\cup T)\le g(S)+g(T)$ for all $S,T\subseteq M$;
--   4. for every $J\in\binom Uk$ and every edge set $D\subseteq\bigcup_{r\in J}\delta_H(r)$ (every edge of $D$ meets $J$),
--   $$
--   |D|+g(M\setminus D)\;\le\;\beta m+m-|E(H-J)|\;\le\;m\Big(1-\frac{2}{e^2}+\frac1{e^3}+\frac1k\Big).
--   $$
--
--   The chain gives the residual bound (22) of Lemma 5.2 for this particular $g$, with an error $1/k$ uniform in $J$ and $D$. In the impossibility instance, $J$ collects the early buyers' type vertices and $D$ their allocated edges, and the left side bounds the expected welfare given the early history.
--
--   Differences from the source:
--   - encoding: vertex set U with |U| = k², edges (U choose k) → U = Fin (k²), edges and k-vertex sets as the subtype of k-element Finsets; reason: relabeling of the vertices, same instances
--   - encoding: g in (33) as a minimum over q ∈ ℤ≥0 and tuples J_1, …, J_q → minimum over finite sets 𝒥 of k-vertex sets of |𝒥|βm + |S \ ⋃_{J∈𝒥} E(H − J)|; reason: repeating a bulk piece only adds βm, as the source notes, so both minima are equal
--   - encoding: the closing clause "in particular, it satisfies (22)" → not restated; reason: it is the transitive consequence of the two stated inequalities
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed pp.22–23, PDF pp.23–24, Proposition 5.3; g from (33), printed p.22, PDF p.23; β printed p.21, PDF p.22.

import Definitions.Def_SubadditiveProphet1456_Quarter_Supplement_Hypergraph

open scoped BigOperators

namespace SubadditiveProphet1456.Quarter.Supplement

/-- STOC 2027 #1456, Proposition 5.3, printed pp. 22–23 (PDF 23–24). `g = coverValue k` is the
covering valuation (33) with `β = (e − 1)²/e³`; `M = univ`, `m = edgeCount k`. -/
theorem proposition_5_3 (k : ℕ) (hk : 2 ≤ k) :
    coverValue k ∅ = 0 ∧
    (∀ S T : Finset (KSubset k), S ⊆ T → coverValue k S ≤ coverValue k T) ∧
    (∀ S T : Finset (KSubset k), coverValue k (S ∪ T) ≤ coverValue k S + coverValue k T) ∧
    ∀ (J : KSubset k) (D : Finset (KSubset k)), D ⊆ J.1.biUnion (incident k) →
      (D.card : ℝ) + coverValue k (Finset.univ \ D) ≤
          coverBeta * (edgeCount k : ℝ) + (edgeCount k : ℝ) - ((avoidEdges k J.1).card : ℝ) ∧
        coverBeta * (edgeCount k : ℝ) + (edgeCount k : ℝ) - ((avoidEdges k J.1).card : ℝ) ≤
          (edgeCount k : ℝ) *
            (1 - 2 / Real.exp 1 ^ 2 + 1 / Real.exp 1 ^ 3 + 1 / (k : ℝ)) := by sorry

end SubadditiveProphet1456.Quarter.Supplement
