-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_4_3
-- name    : SignFreeOracle.Separation.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:13.765925+00:00
-- url     : https://prove2.me/theorems/173e02b8-0e0b-472d-a4d8-37d4d431b79b
-- title:
--   Lemma 4.3 (corrected: integral construction parameters) — self-similar tree exploration
-- statement:
--   For every sufficiently large admissible $n$, set $K=\sqrt n$ and let $T=\widehat T_{n,K}$. A classical adaptive randomized algorithm starts at the known root under a uniformly random labelling and follows previously exposed neighbouring labels. If its total query budget is $q<2^{\sqrt n}$, then
--   $$\Pr[\text{the exploration reaches a 0-level leaf of }T]\le2^{-2n\log_2n}.$$
--   The event includes leaves exposed in replies as well as queried leaves. It concerns the distinguished outer perfect-tree leaves, rather than arbitrary leaves of attached decorations. Algorithms are finite adaptive decision trees with arbitrary internal fair randomness, so they include all rooted local explorers, not just random walks.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
--   - encoding: rooted local tree exploration → adaptive query trees using the root and previously exposed neighbouring labels, counting discoveries in replies; reason: the standard operational exploration convention, with the same distinguished 0-level target
--   - encoding: neighbour positions i in [d] → zero-based natural positions, returning the queried label beyond the neighbour list; reason: positions outside the source query range have a graph-independent self answer and can be simulated without an oracle query
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 4.3, p. 14 (PDF p. 14)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_Experiments

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity

theorem lemma_4_3 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    let T := selfSimilar n (Nat.sqrt n)
    ∀ (root : Fin T.size), root.val = 0 →
    ∀ (q : ℕ) (A : RandomQuery (Fin T.size × ℕ) (Fin T.size) (Fin T.size)),
      q < 2 ^ Nat.sqrt n → A.budget q → RootLocal (treeGraph T) A root →
      permMean (fun π => traceProbability A (anyGraphQuery (treeGraph T) π) (π root)
        (fun history => (π.symm (π root)).val ∈ T.marked ∨
          ∃ e ∈ history, (π.symm e.1.1).val ∈ T.marked ∨ (π.symm e.2).val ∈ T.marked)) ≤
        (2 : ℝ) ^ (-2 * (n : ℝ) * logN n) := by sorry

end SignFreeOracle.Separation
