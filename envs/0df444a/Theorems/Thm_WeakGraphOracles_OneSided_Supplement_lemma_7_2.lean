-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_lemma_7_2
-- name    : WeakGraphOracles.OneSided.Supplement.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:24.128201+00:00
-- url     : https://prove2.me/theorems/965d4eea-7ef4-4084-9735-56bf2fb01432
-- title:
--   Lemma 7.2 — GEN1 views of the cyclic construction are within total variation $8q^2/t$
-- statement:
--   Throughout, $H$ is a fixed pattern graph on $k=|V(H)|$ vertices that is eligible in the sense of Section 1.1 (connected, with at least one edge), $n$ is the number of vertices of the input, $t=\lfloor n^{1/(2k+2)}\rfloor$, and $R$ is a $t$-regular graph of girth larger than $k$ on $r$ vertices with $0<r\le 4k\,t^{k}$ (a graph of the kind supplied by the cited Fact 5.1). $H$ contains a cycle, and $G_{far}$, $G_{free}$ are the graphs of Lemma 7.1 (disjoint blow-ups $H(t)$, respectively disjoint copies of $R$, each with $n-n_1$ isolated vertices). Let $D_{no}$ and $D_{yes}$ be uniformly random relabelings of $G_{far}$ and $G_{free}$.
--
--   There is $N$ such that for every $n\ge N$, every such $R$, every $q$ and every randomized adaptive GEN1 algorithm $A$ making at most $q$ queries,
--
--   $$d_{TV}\big(\mathrm{view}_A(D_{no}),\,\mathrm{view}_A(D_{yes})\big)\ \le\ \frac{8q^2}{t}.$$
--
--   Here the view consists of the algorithm's coins and its complete run (all queries, all replies and the decision). This indistinguishability bound turns Lemma 7.1 into the query lower bound of Theorem 9.
--
--   Differences from the source:
--   - generalization: R is the t-regular girth->k graph R_{t,k} given by Fact 5.1, with r = |V(R)| ≤ 4k t^k → the statement holds for every nonempty t-regular graph R of girth > k on r ≤ 4k t^k vertices; reason: the proof uses only these properties of R; the graph of Fact 5.1 is one such R, so the Lean statement specializes to the source's
--   - encoding: let n be sufficiently large (Sections 7.5–7.6) → ∃ N, ∀ n ≥ N; reason: the section's standing largeness assumption, with the threshold fixed before n, R and the algorithm
--   - encoding: vertex-disjoint copies of H(t) / R plus isolated vertices (unlabeled) → explicit copies on labels 0,…,n₁−1 (copy x / (kt), class (x mod kt)/t; resp. copy x / r, vertex x mod r), labels ≥ n₁ isolated; reason: one concrete labeling; every statement using it is invariant under relabeling or uses the uniform relabeling law
--   - encoding: GEN1 algorithm making q queries → an arbitrary probability distribution over adaptive query trees of depth at most q over the published GEN1 query/reply alphabet; reason: the published protocol layer; it covers all internal randomization and early stopping
--   - encoding: view_A(D): what algorithm A sees on an input drawn from D → joint law of A's coins (its chosen deterministic plan) and its complete run (decision and query/reply transcript), with the input drawn from the uniform relabeling law; reason: the view of a randomized algorithm is its coins together with the answers; total variation is ½ Σ|μ(x) − ν(x)| of these discrete laws
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 19 (PDF p. 20), Lemma 7.2, setting §7.5 p. 18 (PDF p. 19); proof p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_constructions

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Lemma 7.2, printed p. 19 (PDF p. 20), in the setting of Section 7.5 (as in
Lemma 7.1). `D_no`, `D_yes` are uniformly random relabelings of `G_far`,
`G_free`. For every randomized adaptive GEN1 policy making at most `q`
queries, the views (coins and complete run) are within total variation
`8q²/t`. -/
theorem lemma_7_2 (H : Pattern) (hH : EligiblePattern H) (hcyc : ¬ H.graph.IsAcyclic) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (r : ℕ) (R : SimpleGraph (Fin r)),
      ComparisonGraph H.order (sectionT H.order n) R →
      ∀ (q : ℕ) (A : Policy n q),
        tvDist (view (fun G : SimpleGraph (Fin n) => oracle G) A (relabelLaw (caseAFar H n r)))
            (view (fun G : SimpleGraph (Fin n) => oracle G) A (relabelLaw (caseAFree H n R)))
          ≤ 8 * (q : ℝ) ^ 2 / (sectionT H.order n : ℝ) := by sorry

end WeakGraphOracles.OneSided.Supplement
