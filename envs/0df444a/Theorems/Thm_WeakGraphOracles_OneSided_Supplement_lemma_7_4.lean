-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_lemma_7_4
-- name    : WeakGraphOracles.OneSided.Supplement.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:20.32244+00:00
-- url     : https://prove2.me/theorems/eda33641-7a2f-4347-b620-70b1240ce9ff
-- title:
--   Lemma 7.4 — both induced-freeness constructions: free comparison graph, $2c|E(G_{far})|$ edits, farness $c/2$
-- statement:
--   Throughout, $H$ is a fixed pattern graph on $k=|V(H)|$ vertices that is eligible in the sense of Section 1.1 (connected, with at least one edge), $n$ is the number of vertices of the input, $t=\lfloor n^{1/(2k+2)}\rfloor$, and $R$ is a $t$-regular graph of girth larger than $k$ on $r$ vertices with $0<r\le 4k\,t^{k}$ (a graph of the kind supplied by the cited Fact 5.1). Let $c=2^{-k}k^{-4}$.
--
--   *Case A* ($H$ contains a cycle): $n_1$ is the largest multiple of $ktr$ with $n_1\le n$; $G_{far}$ is $n_1/(kt)$ disjoint copies of the blow-up $H(t)$ and $G_{free}$ is $n_1/r$ disjoint copies of $R$, each with $n-n_1$ isolated vertices.
--
--   *Case B* ($H$ is a tree on $k\ge3$ vertices): $n_1=r\lfloor n/r\rfloor$; $G_{far}$ is $\lfloor n/r\rfloor$ disjoint copies of $R$ with $n-n_1$ isolated vertices, and $G_{free}=K_n$.
--
--   There is $N$ such that for every $n\ge N$ and every such $R$, in both cases:
--
--   1. $G_{free}$ has no induced copy of $H$;
--   2. every graph $G'$ on $V(G_{far})$ without an induced copy of $H$ satisfies
--   $$|E(G_{far})\oplus E(G')|\ \ge\ 2c\,|E(G_{far})|;$$
--   3. consequently $\mathrm{dist}_\oplus(G_{far},G')\ge\epsilon_H:=c/2$ for every induced-$H$-free $G'$, that is, $G_{far}$ is $\epsilon_H$-far from induced $H$-freeness with respect to $\mathrm{dist}_\oplus$.
--
--   These are the yes- and far-instances of the lower bound of Theorem 10.
--
--   Differences from the source:
--   - generalization: R is the t-regular girth->k graph R_{t,k} given by Fact 5.1, with r = |V(R)| ≤ 4k t^k → the statement holds for every nonempty t-regular graph R of girth > k on r ≤ 4k t^k vertices; reason: the proof uses only these properties of R; the graph of Fact 5.1 is one such R, so the Lean statement specializes to the source's
--   - encoding: let n be sufficiently large (Sections 7.5–7.6) → ∃ N, ∀ n ≥ N; reason: the section's standing largeness assumption, with the threshold fixed before n, R and the algorithm
--   - encoding: vertex-disjoint copies of H(t) / R plus isolated vertices (unlabeled) → explicit copies on labels 0,…,n₁−1 (copy x / (kt), class (x mod kt)/t; resp. copy x / r, vertex x mod r), labels ≥ n₁ isolated; reason: one concrete labeling; every statement using it is invariant under relabeling or uses the uniform relabeling law
--   - encoding: G is ε-far from P: its dist⊕ distance to the closest graph of P is at least ε → ε ≤ dist⊕(G, G') for every G' ∈ P on the same labels; reason: same condition (finitely many graphs, the minimum is attained); an empty P makes every graph far, the +∞ convention
--   - encoding: H a graph on k vertices (Section 1.1: connected, no isolated vertex); Case A: H contains a cycle; Case B: H is a tree, k ≥ 3 → EligiblePattern H; Case A under ¬ H.graph.IsAcyclic, Case B under H.graph.IsTree and 3 ≤ H.order; reason: the two cases of Section 7.6 as hypotheses of the two conjuncts
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), pp. 20–21 (PDF pp. 21–22), Lemma 7.4 (p. 20 / PDF p. 21), with Cases A and B and the parameters of §7.6, pp. 19–20 (PDF pp. 20–21); proof pp. 20–21 (PDF pp. 21–22)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_constructions

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Lemma 7.4, printed p. 20 (PDF p. 21), both cases of Section 7.6. `H` is
eligible on `k` vertices, `n` large, `t = ⌊n^{1/(2k+2)}⌋`, `R` any `t`-regular
graph of girth `> k` on `r ≤ 4k t^k` vertices, `c = 2^{-k} k^{-4}`.
Case A (`H` has a cycle): `G_far` = disjoint `H(t)` copies, `G_free` = disjoint
`R` copies, same isolated vertices. Case B (`H` a tree on `k ≥ 3` vertices):
`G_far` = `⌊n/r⌋` copies of `R` plus isolated vertices, `G_free = K_n`.
In both cases: (1) `G_free` is induced-`H`-free; (2) every induced-`H`-free `G'`
differs from `G_far` on at least `2c|E(G_far)|` pairs; (3) `G_far` is
`c/2`-far from induced `H`-freeness in `dist⊕`. -/
theorem lemma_7_4 (H : Pattern) (hH : EligiblePattern H) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (r : ℕ) (R : SimpleGraph (Fin r)),
      ComparisonGraph H.order (sectionT H.order n) R →
      (¬ H.graph.IsAcyclic →
        InducedFree {H} (caseAFree H n R) ∧
        (∀ G' : SimpleGraph (Fin n), InducedFree {H} G' →
          2 * inducedConst H.order * ((edges (caseAFar H n r)).card : ℝ) ≤
            symmDiffCard (caseAFar H n r) G') ∧
        DistFar (fun G' => InducedFree {H} G') (inducedConst H.order / 2) (caseAFar H n r)) ∧
      (H.graph.IsTree → 3 ≤ H.order →
        InducedFree {H} (⊤ : SimpleGraph (Fin n)) ∧
        (∀ G' : SimpleGraph (Fin n), InducedFree {H} G' →
          2 * inducedConst H.order * ((edges (caseBFar n R)).card : ℝ) ≤
            symmDiffCard (caseBFar n R) G') ∧
        DistFar (fun G' => InducedFree {H} G') (inducedConst H.order / 2) (caseBFar n R)) := by sorry

end WeakGraphOracles.OneSided.Supplement
