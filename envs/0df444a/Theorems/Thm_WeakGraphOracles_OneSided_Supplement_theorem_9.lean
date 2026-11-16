-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_theorem_9
-- name    : WeakGraphOracles.OneSided.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:08.154106+00:00
-- url     : https://prove2.me/theorems/54cf95f9-c666-4939-9f77-f14de1f33423
-- title:
--   Theorem 9 — cyclic $H$-freeness is not two-sided testable in GEN1, with an $\Omega(n^{1/(4k+4)})$ bound
-- statement:
--   Let $H$ be a fixed graph on $k$ vertices that contains a cycle; as throughout the paper (Section 1.1), $H$ is connected and has no isolated vertex. A graph is $H$-free when it has no (not necessarily induced) copy of $H$, and, $H$-freeness being monotone, $G$ is $\epsilon$-far from it when more than $\epsilon|E(G)|$ edges must be deleted (Section 3).
--
--   Then $H$-freeness is not two-sided error testable in GEN1 (random-neighbour and random-edge queries, $n$ known): no query bound depending on $\epsilon$ alone admits, for every $n$, a GEN1 tester that accepts every $H$-free graph with probability at least $2/3$ and rejects every $\epsilon$-far graph with probability at least $2/3$. Quantitatively, for every $0<\epsilon<1/|E(H)|$ there are $c>0$ and $N$ such that for every $n\ge N$ every such two-sided $\epsilon$-tester on $n$-vertex graphs making $q$ queries satisfies
--
--   $$q\ \ge\ c\,n^{1/(4k+4)}.$$
--
--   This is the two-sided counterpart of Observation 1: for single forbidden subgraphs one-sided and two-sided testability coincide in GEN1. It is informal Theorem 3, whose $n^{\Omega(1)}$ rate is the displayed bound.
--
--   Differences from the source:
--   - encoding: H a fixed graph on k vertices containing a cycle (Section 1.1: connected, no isolated vertex) → EligiblePattern H (connected, at least one edge) and ¬ H.graph.IsAcyclic; reason: the standing assumption of Section 1.1 as encoded by the published base definitions
--   - encoding: testable: a tester with query complexity independent of n → ∀ ε > 0, ∃ q, ∀ n, ∃ one policy of depth ≤ q correct on every n-vertex graph; reason: Definition 1 and Remark 2: a non-uniform family of testers, one per n, with ε wired in
--   - encoding: GEN1 algorithm making q queries → an arbitrary probability distribution over adaptive query trees of depth at most q over the published GEN1 query/reply alphabet; reason: the published protocol layer; it covers all internal randomization and early stopping
--   - generalization: not 2-sided error testable (informal Theorem 3 adds an unspecified n^{Ω(1)} rate) → ¬ testable, and in addition for every 0 < ε < 1/|E(H)| a bound q ≥ c·n^{1/(4k+4)} with c, N fixed before n and the tester; reason: the explicit exponent 1/(4k+4) is the rate the proof in Section 7.5 establishes (Lemma 7.2: q ≥ √(t/24), t = ⌊n^{1/(2k+2)}⌋), stronger than the printed statement; dropping the second conjunct gives exactly the source's Theorem 9
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 10 (PDF p. 11), Theorem 9; informal version p. 2 (PDF p. 3), Theorem 3; proof §7.5, pp. 18–19 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_constructions

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Theorem 9, printed p. 10 (PDF p. 11), with the rate of its proof (Section 7.5)
and of informal Theorem 3 (`n^{Ω(1)}`). `H` is eligible (connected, with an
edge), has `k` vertices and contains a cycle. `H`-freeness (not necessarily
induced) with strict edge-deletion farness is not two-sided error testable in
GEN1; quantitatively, for every `0 < ε < 1/|E(H)|` every two-sided `ε`-tester
on large `n` makes at least `c · n^{1/(4k+4)}` queries, `c > 0` and the
threshold fixed before `n` and the tester. -/
theorem theorem_9 (H : Pattern) (hH : EligiblePattern H) (hcyc : ¬ H.graph.IsAcyclic) :
    ¬ GEN1TwoSidedTestable (fun _ G => Free {H} G) (fun ε _ G => EdgeFar {H} ε G) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / ((edges H.graph).card : ℝ) →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (q : ℕ) (A : Policy n q),
        TwoSidedCorrect (fun G : SimpleGraph (Fin n) => oracle G)
            (fun G => Free {H} G) (fun G => EdgeFar {H} ε G) A →
          c * (n : ℝ) ^ ((1 : ℝ) / (4 * (H.order : ℝ) + 4)) ≤ q := by sorry

end WeakGraphOracles.OneSided.Supplement
