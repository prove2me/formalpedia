-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_4_2
-- name    : RWCuckoo.Threshold.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:19.223593+00:00
-- url     : https://prove2.me/theorems/adfee332-fc0f-4bb2-9c4e-6207713ba74e
-- title:
--   Lemma 4.2 — visitation lemma: E T^frozen ≤ C(1 + E N_G) for every matching and every dense set G
-- statement:
--   There is an absolute constant $C$ such that for all $d\ge3$ and $\varepsilon^*_d<\varepsilon\le1$, on a hash-only event of probability $1-O(1/n)$ (absolute constant, $n$ large), simultaneously for every matching $M$ of the $m=\lfloor(1-\varepsilon)n\rfloor$ keys and every set $G$ of at least $7m/10$ occupied cells,
--   $$\mathbb E\,T^{\mathrm{frozen}}\le C\,(1+\mathbb E\,N_G).$$
--   If $d\ge10^6$, the same holds for every set $G$ of at least $m/2$ occupied cells.
--
--   In words, apart from an additive constant the frozen-matching walk spends a constant fraction of its time in every dense set; this is the second tool of the paper.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - reading: 'the same holds' for |G| ≥ m/2 when d ≥ 10^6 → one event carrying both clauses: |G| ≥ 7m/10, or d ≥ 10^6 and |G| ≥ m/2; reason: 'the same' refers to the same hash-only event and the same C
--   - encoding: E T^frozen, E T^fresh, E N_G (expectation over the walk, for fixed hashes and matching) → lintegral in ℝ≥0∞ of the ℕ∞-valued walk length or visit count against the uniform first cell × an i.i.d. uniform probe stream ℕ → Fin d (⊤ if the walk never stops); reason: the walk randomness of Definitions 2.1 and 5.3; expectations of possibly infinite lengths live in ℝ≥0∞
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 14 (PDF 15), Lemma 4.2

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 4.2, the visitation lemma (p. 14): there is an absolute constant `C` such that for all
`d ≥ 3` and `ε∗_d < ε ≤ 1`, on a hash-only event of probability `1 − O(1/n)` (absolute constant,
`n` large), simultaneously for every matching and every set `G` of at least `7m/10` occupied cells
(or of at least `m/2` occupied cells if `d ≥ 10^6`), `E T^frozen ≤ C (1 + E N_G)`. -/
theorem lemma_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ (M : Matching h) (G : Finset (Fin n)), G ⊆ M.occupied →
              (7 * (numKeys n ε : ℝ) / 10 ≤ G.card ∨
                ((10 : ℕ) ^ 6 ≤ d ∧ (numKeys n ε : ℝ) / 2 ≤ G.card)) →
              expFrozenTime M ≤ ENNReal.ofReal C * (1 + expFrozenVisits M G)} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
