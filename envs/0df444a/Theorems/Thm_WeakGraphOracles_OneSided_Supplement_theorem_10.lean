-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_theorem_10
-- name    : WeakGraphOracles.OneSided.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:41.652297+00:00
-- url     : https://prove2.me/theorems/feb7e55c-518a-4afd-93aa-12c69b9299f3
-- title:
--   Theorem 10 — induced $K_2$-freeness takes one query; every other induced $H$-freeness needs $\Omega(n^{1/(4k+4)})$ two-sided GEN1 queries
-- statement:
--   Let $H$ be a graph on $k$ vertices, connected and without isolated vertices as throughout the paper (Section 1.1). A graph is induced $H$-free when it has no induced copy of $H$; this property is not monotone, and farness is measured by $\mathrm{dist}_\oplus$: $G$ is $\epsilon$-far when $\mathrm{dist}_\oplus(G,G')\ge\epsilon$ for every induced-$H$-free $G'$.
--
--   1. If $H\cong K_2$, then induced $H$-freeness is testable in GEN1 with one query: for every $\epsilon>0$ and every $n$ there is a GEN1 policy making one query that accepts every induced-$K_2$-free (edgeless) graph and rejects every $\epsilon$-far graph, each with probability at least $2/3$.
--   2. Otherwise there is $\epsilon_H>0$ such that for every $0<\epsilon<\epsilon_H$ there are $c>0$ and $N$ with the following property: for every $n\ge N$, every two-sided error $\epsilon$-tester for induced $H$-freeness in GEN1 on $n$-vertex graphs making $q$ queries satisfies
--   $$q\ \ge\ c\,n^{1/(4k+4)}.$$
--
--   Together with Theorem 11 this is informal Theorem 4: among single forbidden induced subgraphs, only $K_2$ gives a two-sided testable property in GEN1.
--
--   Differences from the source:
--   - encoding: H a graph on k vertices (Section 1.1: connected, no isolated vertex); H = K2 → EligiblePattern H; H = K2 as a graph isomorphism H.graph ≃g ⊤ on Fin 2; reason: the standing assumption of Section 1.1; equality of graphs is up to isomorphism
--   - encoding: Ω(n^{1/(4k+4)}) queries for every ε < ε_H; an ε-tester has ε > 0 (Definition 1) → for every 0 < ε < ε_H, q ≥ c·n^{1/(4k+4)} for all n ≥ N, with c > 0 and N chosen after ε and before n and the tester; reason: the definition of Ω with its constants independent of n and of the tester, and the standing positive proximity domain of Definition 1
--   - encoding: G is ε-far from P: its dist⊕ distance to the closest graph of P is at least ε → ε ≤ dist⊕(G, G') for every G' ∈ P on the same labels; reason: same condition (finitely many graphs, the minimum is attained); an empty P makes every graph far, the +∞ convention
--   - encoding: GEN1 algorithm making q queries → an arbitrary probability distribution over adaptive query trees of depth at most q over the published GEN1 query/reply alphabet; reason: the published protocol layer; it covers all internal randomization and early stopping
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 11 (PDF p. 12), Theorem 10; informal version p. 2 (PDF p. 3), Theorem 4; proof §7.6, pp. 19–21 (PDF pp. 20–22)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Theorem 10, printed p. 11 (PDF p. 12). `H` is eligible (connected, with an
edge) on `k` vertices; farness from induced `H`-freeness is in `dist⊕`.
If `H ≅ K₂`, induced `H`-freeness is testable in GEN1 with one query (for every
`ε > 0` and every `n`). Otherwise there is `ε_H > 0` such that for every
`0 < ε < ε_H` every two-sided GEN1 `ε`-tester on large `n` makes at least
`c · n^{1/(4k+4)}` queries, `c > 0` and the threshold fixed before `n` and the
tester. -/
theorem theorem_10 (H : Pattern) (hH : EligiblePattern H) :
    (Nonempty (H.graph ≃g (⊤ : SimpleGraph (Fin 2))) →
      ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∃ A : Policy n 1,
        TwoSidedCorrect (fun G : SimpleGraph (Fin n) => oracle G)
          (fun G => InducedFree {H} G)
          (DistFar (fun G' => InducedFree {H} G') ε) A) ∧
    (IsEmpty (H.graph ≃g (⊤ : SimpleGraph (Fin 2))) →
      ∃ εH : ℝ, 0 < εH ∧ ∀ ε : ℝ, 0 < ε → ε < εH →
        ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (q : ℕ) (A : Policy n q),
          TwoSidedCorrect (fun G : SimpleGraph (Fin n) => oracle G)
              (fun G => InducedFree {H} G)
              (DistFar (fun G' => InducedFree {H} G') ε) A →
            c * (n : ℝ) ^ ((1 : ℝ) / (4 * (H.order : ℝ) + 4)) ≤ q) := by sorry

end WeakGraphOracles.OneSided.Supplement
