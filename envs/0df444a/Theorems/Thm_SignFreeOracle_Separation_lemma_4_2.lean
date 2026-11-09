-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_4_2
-- name    : SignFreeOracle.Separation.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:35.131886+00:00
-- url     : https://prove2.me/theorems/743bdbaf-c922-4b44-b1bb-c4f6fadc1302
-- title:
--   Lemma 4.2 (corrected: integral construction parameters) — local exploration
-- statement:
--   For every sufficiently large admissible $n$, fix a seed set $U$ of size at most half the full label universe, an injective labelling of $U$, and either $G_n$ or $F_n(U)$. Let $A$ receive the fixed seed labels and make at most $q$ arbitrary adaptive graph queries. Under a uniformly random extension of the partial labelling, including private algorithm randomness, the exceptional probability is at most
--   $$q\,2^{-2n^3\log_2^2n}.$$
--   Outside this event, no fresh query guesses a nonisolated YES vertex before that label has been exposed. At every execution prefix, the queried addresses together with the seeds induce components rooted at seeds, together with isolates. Addresses, earlier answers and seeds are separate in the event definitions. This is a probabilistic conclusion about arbitrary query trees.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
--   - generalization: the queried vertices induce components rooted at the seed, apart from YES-isolates → the rooted-component conclusion and a bound on guessing any previously unexposed nonisolated vertex; reason: the fresh-query event also counts guesses landing next to an existing component; its bound strengthens the printed conclusion and implies it by following earlier replies
--   - encoding: neighbour positions i in [d] → zero-based natural positions, returning the queried label beyond the neighbour list; reason: positions outside the source query range have a graph-independent self answer and can be simulated without an oracle query
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 4.2, p. 13 (PDF p. 13)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_Experiments

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity

theorem lemma_4_2 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
    ∀ (U : Set (Fin (2 ^ bits n))) (σ : PartialLabel (2 ^ bits n)),
      U.ncard ≤ 2 ^ bits n / 2 → (∀ v, (σ.val v).isSome ↔ v ∈ U) →
    ∀ (G : SimpleGraph (Fin (2 ^ bits n))), G = yesGraph n NB B ∨ G = noGraph n NB B U →
    ∀ (q : ℕ) (A : RandomQuery (Fin (2 ^ bits n) × ℕ) (Fin (2 ^ bits n))
        (Finset (Fin (2 ^ bits n)))), A.budget q →
      extensionMean σ (fun π => traceProbability A (anyGraphQuery G π) (fixedSeed σ)
        (fun history => FreshNonisolated (yesGraph n NB B) π (fixedSeed σ : Set _) history ∨
          ¬ RootedAddresses G π (fixedSeed σ : Set _) history)) ≤
        q * (2 : ℝ) ^ (-2 * (n : ℝ) ^ 3 * (logN n) ^ 2) := by sorry

end SignFreeOracle.Separation
