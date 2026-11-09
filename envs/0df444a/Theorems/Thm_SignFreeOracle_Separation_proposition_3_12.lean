-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_proposition_3_12
-- name    : SignFreeOracle.Separation.proposition_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:03.095666+00:00
-- url     : https://prove2.me/theorems/5e956106-1788-4d81-bc73-b856f81c9893
-- title:
--   Proposition 3.12 (corrected: integral construction parameters) — small Perron eigenvalue
-- statement:
--   For every sufficiently large admissible integral parameter $n$, every base graph with the original bounds, and every seed set $U$ of at most $2^{\sqrt n}$ vertices,
--   $$\lambda_{\max}(F_n(U))\le4\sqrt n.$$
--   The constant is exactly four, and the full-size NO graph is the one constructed from the seed closure and the extra base-only boundary layer. Empty seeds and isolates are included. Together with Lemma 3.9, this supplies the original spectral separation.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Proposition 3.12, p. 12 (PDF p. 12)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_MA

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

theorem proposition_3_12 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
      ∀ U : Set (Fin (2 ^ bits n)), U.ncard ≤ 2 ^ Nat.sqrt n →
        perron (noGraph n NB B U) ≤ 4 * Real.sqrt n := by sorry

end SignFreeOracle.Separation
