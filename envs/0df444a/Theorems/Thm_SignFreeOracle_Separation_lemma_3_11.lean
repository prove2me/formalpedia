-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_3_11
-- name    : SignFreeOracle.Separation.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:09.675136+00:00
-- url     : https://prove2.me/theorems/c7a8354f-6392-4404-a906-0f9e7712ffd8
-- title:
--   Lemma 3.11 (corrected: integral construction parameters) — 2-degeneracy
-- statement:
--   For every sufficiently large admissible integral $n$, every base graph with the original bounds, and every seed set $U$ in the full vertex universe with $|U|\le2^{\sqrt n}$,
--   $$F_n(U)\text{ is 2-degenerate}.$$
--   The seed may be empty and may contain tree vertices or padded isolates. The graph retains the same full vertex set as $G_n$ and exactly the prescribed induced-neighbourhood edges. Degeneracy quantifies over every nonempty subgraph, through its equivalent induced-set formulation. This is a structural conclusion, not an assumed property of a supplied NO graph.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 3.11, p. 12 (PDF p. 12)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_MA

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

theorem lemma_3_11 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
      ∀ U : Set (Fin (2 ^ bits n)), U.ncard ≤ 2 ^ Nat.sqrt n →
        Degenerate (noGraph n NB B U) 2 := by sorry

end SignFreeOracle.Separation
