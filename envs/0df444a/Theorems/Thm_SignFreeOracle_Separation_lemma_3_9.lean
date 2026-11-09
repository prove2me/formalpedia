-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_3_9
-- name    : SignFreeOracle.Separation.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:32.56536+00:00
-- url     : https://prove2.me/theorems/f69aa160-8c41-47fa-a43a-06154e30136c
-- title:
--   Lemma 3.9 (corrected: integral construction parameters) — large Perron eigenvalue
-- statement:
--   For every sufficiently large admissible integral parameter $n$, and every base graph $B$ with the original connectedness, regularity, girth and size bounds, the actual recursively decorated graph $G_n(B)$ satisfies
--   $$\lambda_{\max}(G_n(B))\ge n.$$
--   The construction package also asserts that all nonisolated vertices fit within the specified $2^{m(n)}$ labels, so isolate padding does not discard a constructed vertex. The threshold precedes the base graph. This is the YES spectral promise on the original decorated graph, and includes the size fact stated in Definition 3.7.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
--   - generalization: the Perron lower bound in Lemma 3.9 and the size guarantee in Definition 3.7 → both the Perron bound and the assertion that all constructed vertices fit the full label universe; reason: the size conclusion makes isolate padding auditable and assumes no size bound beyond the source base bounds
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 3.9, p. 11 (PDF p. 11)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_MA

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

theorem lemma_3_9 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
      nonisolatedSize n NB ≤ 2 ^ bits n ∧ (n : ℝ) ≤ perron (yesGraph n NB B) := by sorry

end SignFreeOracle.Separation
