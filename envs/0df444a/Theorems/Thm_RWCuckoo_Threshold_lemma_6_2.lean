-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_6_2
-- name    : RWCuckoo.Threshold.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:33:18.176884+00:00
-- url     : https://prove2.me/theorems/11ebb63e-f97d-4b21-b279-1faf6141b584
-- title:
--   Lemma 6.2 — constant-factor expansion |N(A)| = Ω(d|A|) for e^{−d/3}n ≤ |A| ≤ n/d
-- statement:
--   There are absolute constants $D_0$, $c>0$, $C$ such that for $d\ge D_0$ and $\varepsilon^*_d<\varepsilon<e^{-d/4}$, for all large $n$, with probability at least $1-C/n$ over the hashes of the $m$ keys: for every matching, every set $A$ of cells with $e^{-d/3}n\le|A|\le n/d$ satisfies
--   $$|N(A)|\ge c\,d\,|A| .$$
--
--   It is the "straightforward" expansion bound of §6.2, used as a fallback for a bounded number of levels.
--
--   Differences from the source:
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 23 (PDF 24), Lemma 6.2

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk
import Definitions.Def_RWCuckoo_Threshold_Expansion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 6.2 (p. 23): for `d ≥ D0` and `ε∗_d < ε < e^{−d/4}`, w.h.p., for every matching, every
set `A` of cells with `e^{−d/3} n ≤ |A| ≤ n/d` satisfies `|N(A)| ≥ c d |A|`, `c` absolute. -/
theorem lemma_6_2 :
    ∃ D0 : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε →
      ε < Real.exp (-(d : ℝ) / 4) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ (M : Matching h) (A : Finset (Fin n)),
              Real.exp (-(d : ℝ) / 3) * n ≤ A.card → (A.card : ℝ) ≤ n / d →
              c * d * A.card ≤ (M.nbhd A).card} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
