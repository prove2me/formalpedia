-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_theorem_4_4
-- name    : SignFreeOracle.Separation.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:59.802205+00:00
-- url     : https://prove2.me/theorems/9ffe71df-9b5d-402e-9e57-a68bdfeeb2bb
-- title:
--   Theorem 4.4 (corrected: integral construction parameters) — classical indistinguishability
-- statement:
--   Fix a sufficiently large admissible $n$, a valid base graph, any seed $U$ of size at most $2^{\sqrt n}$, and any injective partial labelling of that seed. Every randomized adaptive algorithm receiving the seed labels and making at most $q<2^{\sqrt n}$ adjacency-list queries satisfies
--   $$\left|\Pr[A^{O_{G_n,\pi}}(\pi(U))=1]-\Pr[A^{O_{F_n(U),\pi}}(\pi(U))=1]\right|\le2^{-n\log_2n}.$$
--   Each probability averages over uniform extensions of the same fixed partial labelling and over algorithm randomness. Queries may address arbitrary labels; no locality hypothesis is present. This is the full label-fixing indistinguishability statement used against arbitrary witnesses.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
--   - encoding: neighbour positions i in [d] → zero-based natural positions, returning the queried label beyond the neighbour list; reason: positions outside the source query range have a graph-independent self answer and can be simulated without an oracle query
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Theorem 4.4, p. 14 (PDF p. 14)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_Experiments

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity

theorem theorem_4_4 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
    ∀ (U : Set (Fin (2 ^ bits n))) (σ : PartialLabel (2 ^ bits n)),
      U.ncard ≤ 2 ^ Nat.sqrt n → (∀ v, (σ.val v).isSome ↔ v ∈ U) →
    ∀ (q : ℕ) (A : RandomQuery (Fin (2 ^ bits n) × ℕ) (Fin (2 ^ bits n))
        (Finset (Fin (2 ^ bits n)))), q < 2 ^ Nat.sqrt n → A.budget q →
      |extensionMean σ (fun π => A.accept (anyGraphQuery (yesGraph n NB B) π) (fixedSeed σ)) -
        extensionMean σ (fun π => A.accept (anyGraphQuery (noGraph n NB B U) π) (fixedSeed σ))| ≤
          (2 : ℝ) ^ (-(n : ℝ) * logN n) := by sorry

end SignFreeOracle.Separation
