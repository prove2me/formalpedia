-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_Supplement_lemma_5_2
-- name    : SubadditiveProphet1456.Quarter.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:45:38.963891+00:00
-- url     : https://prove2.me/theorems/c9c3f9ed-db4f-4b99-bd46-e3c7cc87fcf2
-- title:
--   Lemma 5.2 — One subadditive valuation on the hypergraph edges with the residual bound (22) and the full-set bound (23)
-- statement:
--   Let $k\ge2$ and let $H=(U,M)$ be the complete $k$-uniform hypergraph on $|U|=k^2$ vertices, with $m=|M|=\binom{k^2}{k}$ edges and incident edge sets $\delta_H(r)$. There is a single function $g:2^M\to\mathbb R_{\ge0}$, chosen before $J$ and $D$, such that
--
--   1. $g$ is normalised, $g(\varnothing)=0$;
--   2. $g$ is monotone, $g(S)\le g(T)$ for $S\subseteq T$;
--   3. $g$ is subadditive, $g(S\cup T)\le g(S)+g(T)$;
--   4. for every $J\in\binom Uk$ and every $D\subseteq\bigcup_{r\in J}\delta_H(r)$,
--   $$
--   |D|+g(M\setminus D)\le m\Big(1-\frac2{e^2}+\frac1{e^3}+\frac1k\Big); \tag{22}
--   $$
--   5. and
--   $$
--   g(M)\ge m\Big(1-\frac3{e^2}+\frac2{e^3}-\frac4{k^{1/4}}\Big). \tag{23}
--   $$
--
--   The errors $1/k$ and $4/k^{1/4}$ hold for every $k\ge2$ and do not depend on $J$ or $D$. The lemma supplies the valuation of the final buyer in the impossibility instance: (22) bounds the welfare of every online algorithm, and (23) makes the ex-ante benchmark large.
--
--   Differences from the source:
--   - encoding: g : 2^M → ℝ≥0 → g : Finset (k-subsets of Fin (k²)) → ℝ together with the clause 0 ≤ g S for all S; reason: the same functions
--   - encoding: vertex set U with |U| = k², edges (U choose k) → U = Fin (k²), edges and k-vertex sets as the subtype of k-element Finsets; reason: relabeling, same instances
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.19, PDF p.20, Lemma 5.2, displays (22) and (23); hypergraph notation printed p.18, PDF p.19.

import Definitions.Def_SubadditiveProphet1456_Quarter_Supplement_Hypergraph

open scoped BigOperators

namespace SubadditiveProphet1456.Quarter.Supplement

/-- STOC 2027 #1456, Lemma 5.2, printed p. 19 (PDF 20), displays (22) and (23). One valuation
`g` on sets of edges of the complete `k`-uniform hypergraph on `k²` vertices is chosen before
`J` and `D`. -/
theorem lemma_5_2 (k : ℕ) (hk : 2 ≤ k) :
    ∃ g : Finset (KSubset k) → ℝ,
      (∀ S, 0 ≤ g S) ∧ g ∅ = 0 ∧
      (∀ S T : Finset (KSubset k), S ⊆ T → g S ≤ g T) ∧
      (∀ S T : Finset (KSubset k), g (S ∪ T) ≤ g S + g T) ∧
      (∀ (J : KSubset k) (D : Finset (KSubset k)), D ⊆ J.1.biUnion (incident k) →
        (D.card : ℝ) + g (Finset.univ \ D) ≤
          (edgeCount k : ℝ) * (1 - 2 / Real.exp 1 ^ 2 + 1 / Real.exp 1 ^ 3 + 1 / (k : ℝ))) ∧
      (edgeCount k : ℝ) * (1 - 3 / Real.exp 1 ^ 2 + 2 / Real.exp 1 ^ 3 - 4 / (k : ℝ) ^ (1 / 4 : ℝ)) ≤
        g Finset.univ := by sorry

end SubadditiveProphet1456.Quarter.Supplement
