-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_lemma_7_5
-- name    : WeakGraphOracles.OneSided.Supplement.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:52.748202+00:00
-- url     : https://prove2.me/theorems/55fc0100-f2fc-4dda-89e4-eb3f1e30e20d
-- title:
--   Lemma 7.5 — GEN1 views of the induced constructions are within $8q^2/t+8kq/\sqrt n$
-- statement:
--   Throughout, $H$ is a fixed pattern graph on $k=|V(H)|$ vertices that is eligible in the sense of Section 1.1 (connected, with at least one edge), $n$ is the number of vertices of the input, $t=\lfloor n^{1/(2k+2)}\rfloor$, and $R$ is a $t$-regular graph of girth larger than $k$ on $r$ vertices with $0<r\le 4k\,t^{k}$ (a graph of the kind supplied by the cited Fact 5.1). In both cases of Section 7.6 (Case A: $H$ contains a cycle, $G_{far}$ = disjoint blow-ups $H(t)$, $G_{free}$ = disjoint copies of $R$, each with $n-n_1$ isolated vertices, $n_1$ the largest multiple of $ktr$ at most $n$; Case B: $H$ a tree on $k\ge3$ vertices, $G_{far}$ = $\lfloor n/r\rfloor$ disjoint copies of $R$ plus $n-r\lfloor n/r\rfloor$ isolated vertices, $G_{free}=K_n$) let $D_{no}$, $D_{yes}$ be uniformly random relabelings of $G_{far}$, $G_{free}$.
--
--   There is $N$ such that for every $n\ge N$, every such $R$, every $q$ and every randomized adaptive GEN1 algorithm $A$ making at most $q$ queries,
--
--   $$d_{TV}\big(\mathrm{view}_A(D_{no}),\,\mathrm{view}_A(D_{yes})\big)\ \le\ \frac{8q^2}{t}+\frac{8kq}{\sqrt n}.$$
--
--   The second term accounts for the different numbers of isolated vertices in Case B. With Lemma 7.4 this yields the lower bound of Theorem 10.
--
--   Differences from the source:
--   - generalization: R is the t-regular girth->k graph R_{t,k} given by Fact 5.1, with r = |V(R)| ≤ 4k t^k → the statement holds for every nonempty t-regular graph R of girth > k on r ≤ 4k t^k vertices; reason: the proof uses only these properties of R; the graph of Fact 5.1 is one such R, so the Lean statement specializes to the source's
--   - encoding: let n be sufficiently large (Sections 7.5–7.6) → ∃ N, ∀ n ≥ N; reason: the section's standing largeness assumption, with the threshold fixed before n, R and the algorithm
--   - encoding: vertex-disjoint copies of H(t) / R plus isolated vertices (unlabeled) → explicit copies on labels 0,…,n₁−1 (copy x / (kt), class (x mod kt)/t; resp. copy x / r, vertex x mod r), labels ≥ n₁ isolated; reason: one concrete labeling; every statement using it is invariant under relabeling or uses the uniform relabeling law
--   - encoding: GEN1 algorithm making q queries → an arbitrary probability distribution over adaptive query trees of depth at most q over the published GEN1 query/reply alphabet; reason: the published protocol layer; it covers all internal randomization and early stopping
--   - encoding: view_A(D): what algorithm A sees on an input drawn from D → joint law of A's coins (its chosen deterministic plan) and its complete run (decision and query/reply transcript), with the input drawn from the uniform relabeling law; reason: the view of a randomized algorithm is its coins together with the answers; total variation is ½ Σ|μ(x) − ν(x)| of these discrete laws
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 21 (PDF p. 22), Lemma 7.5, setting §7.6 pp. 19–20 (PDF pp. 20–21); proof p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_constructions

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Lemma 7.5, printed p. 21 (PDF p. 22), both cases of Section 7.6 (setting as in
Lemma 7.4). `D_no`, `D_yes` are uniformly random relabelings of `G_far`,
`G_free`. For every randomized adaptive GEN1 policy making at most `q` queries,
the views (coins and complete run) are within total variation
`8q²/t + 8kq/√n`. -/
theorem lemma_7_5 (H : Pattern) (hH : EligiblePattern H) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (r : ℕ) (R : SimpleGraph (Fin r)),
      ComparisonGraph H.order (sectionT H.order n) R →
      ∀ (q : ℕ) (A : Policy n q),
        (¬ H.graph.IsAcyclic →
          tvDist (view (fun G : SimpleGraph (Fin n) => oracle G) A (relabelLaw (caseAFar H n r)))
              (view (fun G : SimpleGraph (Fin n) => oracle G) A (relabelLaw (caseAFree H n R)))
            ≤ 8 * (q : ℝ) ^ 2 / (sectionT H.order n : ℝ) +
              8 * (H.order : ℝ) * q / Real.sqrt n) ∧
        (H.graph.IsTree → 3 ≤ H.order →
          tvDist (view (fun G : SimpleGraph (Fin n) => oracle G) A (relabelLaw (caseBFar n R)))
              (view (fun G : SimpleGraph (Fin n) => oracle G) A
                (relabelLaw (⊤ : SimpleGraph (Fin n))))
            ≤ 8 * (q : ℝ) ^ 2 / (sectionT H.order n : ℝ) +
              8 * (H.order : ℝ) * q / Real.sqrt n) := by sorry

end WeakGraphOracles.OneSided.Supplement
