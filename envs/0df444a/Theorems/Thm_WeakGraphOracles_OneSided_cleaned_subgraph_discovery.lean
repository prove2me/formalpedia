-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_cleaned_subgraph_discovery
-- name    : WeakGraphOracles.OneSided.cleaned_subgraph_discovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:09.967727+00:00
-- url     : https://prove2.me/theorems/e439b8b1-fb05-4b65-902b-5eb57dbe25a0
-- title:
--   Lemma 4.3 — discovery transfer with the same query bound
-- statement:
--   Fix a connected non-isolated pattern $H$, positive constants $\epsilon_1,p_1$, and an integer query bound $q_1$. Consider any public input class $I$ of graphs together with nonempty edge-disjoint collections $C$ of at least $\epsilon_1|E(G)|$ appearances. Suppose that for each $n$ a single graph-independent $q_1$-query policy discovers $H$ with probability at least $p_1$ in every union of every retained subcollection $C'\subseteq C$ of size at least $\epsilon_1|E(G)|/2$, for every admissible instance in $I$. Then for each $n$ there is a single graph-independent policy using the same $q_1$ queries which, for every original instance in $I$, discovers $H$ with probability
--
--   $$p\ge p_1(\epsilon_1/4)^{q_1}.$$
--
--   The parameters are fixed outside $n$. The policies are chosen before the hidden graph and packing; neither receives the retained subgraph, collection or role map as input. Discovery means an appearance in the edges actually observed. The policies are unrestricted, as in the printed lemma: a policy may query labels it has not discovered, and §7.2's remark that the tester queries only discovered vertices is not assumed. The statement does not assume the conclusion of cleaning.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labels [n] → SimpleGraph (Fin n), with finite patterns carrying their own order; reason: relabeling by the standard bijection preserves every graph, appearance, degree and edge count
--   - encoding: adaptive randomized algorithms with at most q oracle queries → PMF over complete deterministic query plans of depth at most q, executed against fresh uniform response kernels; reason: finite query and reply alphabets at each fixed n and q make this equivalent to arbitrary internal randomization; no hidden graph is supplied to a policy
--   - reading: there is a test for every retained subgraph, followed by a test on the original input → a public instance class I with a shared policy at each n, before all hidden graphs and collections, on both sides; reason: makes the implicit uniformity of a test explicit and prevents selecting a hidden-graph-specific tester
--   - generalization: a collection of epsilon_1|E| appearances → at least epsilon_1 times |E| appearances, with no separate nonemptiness or p_1 at most 1 clause; reason: an exact-size collection is a special case, and exact size has no instance when epsilon_1|E| is not an integer; the §7.2 proof uses only the lower bound; an empty collection or p_1 above 1 already contradicts the premise on any inhabited instance class
--   - reading: a test, with §7.2 remarking that the tester queries only vertices it has already discovered → arbitrary valid q_1-query policies on both sides, including queries at undiscovered labels; reason: the printed lemma states no such restriction, and the stronger of the two readings is kept
--   - encoding: the edge query is undefined on an empty edge set in the displayed oracle description → a distinguished no-edge reply on edgeless inputs, and an isolation reply for empty neighbor sets; reason: completes the operational kernel on all input graphs, consistently with the source K2 discussion; nonempty-edge and neighbor laws are unchanged
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 8 (PDF p. 9), Lemma 4.3; proof pp. 15–16 (PDF pp. 16–17)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_testing

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Lemma 4.3. `I` describes the input class, not information given to
the algorithm. Both tests are chosen before any hidden graph or collection;
the premise covers every retained subcollection, uniformly. The collection has
at least `ε₁ * |E|` copies, as the §7.2 proof uses. The premise already forces
each instance's collection to be nonempty and `p₁ ≤ 1` on any inhabited instance.
The printed lemma says "a test": the policies are unrestricted, and §7.2's
remark about querying discovered vertices is not assumed here. -/
theorem cleaned_subgraph_discovery (H : Pattern) (hH : EligiblePattern H)
    (ε₁ p₁ : ℝ) (hε : 0 < ε₁) (hp : 0 < p₁) (q₁ : ℕ)
    (I : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Finset (Appearance H G) → Prop)
    (hI : ∀ n G C, I n G C → EdgeDisjoint C ∧
      ε₁ * (edges G).card ≤ (C.card : ℝ))
    (hlocal : ∀ n, ∃ A : Policy n q₁, ValidPolicy true A ∧
      ∀ G C, I n G C → ∀ C' : Finset (Appearance H G), C' ⊆ C →
        ε₁ * (edges G).card / 2 ≤ (C'.card : ℝ) →
        p₁ ≤ discoveryProbability H A (copyUnion C')) :
    ∀ n, ∃ A : Policy n q₁, ValidPolicy true A ∧
      ∀ G C, I n G C → p₁ * (ε₁ / 4) ^ q₁ ≤ discoveryProbability H A G := by sorry

end WeakGraphOracles.OneSided
