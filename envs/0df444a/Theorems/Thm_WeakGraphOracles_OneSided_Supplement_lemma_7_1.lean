-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_lemma_7_1
-- name    : WeakGraphOracles.OneSided.Supplement.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:50.236567+00:00
-- url     : https://prove2.me/theorems/a160ccbd-4f34-4bcc-9d20-b85f4d8ccf46
-- title:
--   Lemma 7.1 — the high-girth graph is $H$-free; the blow-up union needs $|E(G_{far})|/e_H$ deletions
-- statement:
--   Throughout, $H$ is a fixed pattern graph on $k=|V(H)|$ vertices that is eligible in the sense of Section 1.1 (connected, with at least one edge), $n$ is the number of vertices of the input, $t=\lfloor n^{1/(2k+2)}\rfloor$, and $R$ is a $t$-regular graph of girth larger than $k$ on $r$ vertices with $0<r\le 4k\,t^{k}$ (a graph of the kind supplied by the cited Fact 5.1). $H$ contains a cycle; $e_H=|E(H)|$. Let $n_1$ be the largest multiple of $ktr$ with $n_1\le n$, let $G_{far}$ be $n_1/(kt)$ disjoint copies of the blow-up $H(t)$ together with $n-n_1$ isolated vertices, and $G_{free}$ be $n_1/r$ disjoint copies of $R$ together with $n-n_1$ isolated vertices.
--
--   There is $N$ such that for every $n\ge N$ and every such $R$:
--
--   1. $G_{free}$ contains no (not necessarily induced) copy of $H$;
--   2. every set $D$ of edges of $G_{far}$ whose deletion makes $G_{far}$ $H$-free satisfies
--   $$|D|\ \ge\ \frac{|E(G_{far})|}{e_H};$$
--   3. consequently $G_{far}$ is $\epsilon$-far from $H$-freeness for every $\epsilon<1/e_H$: more than $\epsilon|E(G_{far})|$ edges must be deleted.
--
--   These are the two graphs whose random relabelings form the distributions of the two-sided lower bound for cyclic $H$ (Theorem 9).
--
--   Differences from the source:
--   - generalization: R is the t-regular girth->k graph R_{t,k} given by Fact 5.1, with r = |V(R)| ≤ 4k t^k → the statement holds for every nonempty t-regular graph R of girth > k on r ≤ 4k t^k vertices; reason: the proof uses only these properties of R; the graph of Fact 5.1 is one such R, so the Lean statement specializes to the source's
--   - encoding: let n be sufficiently large (Sections 7.5–7.6) → ∃ N, ∀ n ≥ N; reason: the section's standing largeness assumption, with the threshold fixed before n, R and the algorithm
--   - encoding: vertex-disjoint copies of H(t) / R plus isolated vertices (unlabeled) → explicit copies on labels 0,…,n₁−1 (copy x / (kt), class (x mod kt)/t; resp. copy x / r, vertex x mod r), labels ≥ n₁ isolated; reason: one concrete labeling; every statement using it is invariant under relabeling or uses the uniform relabeling law
--   - generalization: G_far is ε-far for the fixed ε < 1/|E(H)| of Section 7.5 → G_far is ε-far for every real ε < 1/e_H; reason: the fixed ε of the section is one such value
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 18 (PDF p. 19), Lemma 7.1, with the setting of §7.5 on the same page; proof pp. 18–19 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_constructions

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Lemma 7.1, printed p. 18 (PDF p. 19), in the setting of Section 7.5:
`H` eligible with a cycle, `k = |V(H)|`, `e_H = |E(H)|`, `n` large,
`t = ⌊n^{1/(2k+2)}⌋`, `R` any `t`-regular graph of girth `> k` on
`r ≤ 4k t^k` vertices, `n₁` the largest multiple of `k t r` at most `n`.
(1) `G_free` is `H`-free; (2) every deletion set making `G_far` `H`-free has
at least `|E(G_far)|/e_H` edges; in particular `G_far` is `ε`-far for
every `ε < 1/e_H` (strict edge-deletion farness of Section 3). -/
theorem lemma_7_1 (H : Pattern) (hH : EligiblePattern H) (hcyc : ¬ H.graph.IsAcyclic) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (r : ℕ) (R : SimpleGraph (Fin r)),
      ComparisonGraph H.order (sectionT H.order n) R →
      Free {H} (caseAFree H n R) ∧
      (∀ D : Finset (Sym2 (Fin n)), D ⊆ edges (caseAFar H n r) →
          Free {H} (delete (caseAFar H n r) D) →
          ((edges (caseAFar H n r)).card : ℝ) / (edges H.graph).card ≤ D.card) ∧
      ∀ ε : ℝ, ε < 1 / ((edges H.graph).card : ℝ) → EdgeFar {H} ε (caseAFar H n r) := by sorry

end WeakGraphOracles.OneSided.Supplement
