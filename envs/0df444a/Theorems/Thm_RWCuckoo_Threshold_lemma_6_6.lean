-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_6_6
-- name    : RWCuckoo.Threshold.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:33:05.014515+00:00
-- url     : https://prove2.me/theorems/40fc9258-2fe6-486d-a7d6-7498f749cdf3
-- title:
--   Lemma 6.6 — for every set A of ≥ n/d cells, 3m/5 keys have Ω(d|A|/n) hashes in A
-- statement:
--   There are absolute constants $D_0$, $c>0$ and $C$ such that for $d\ge D_0$ and $\varepsilon^*_d<\varepsilon<e^{-d/4}$, for all large $n$, with probability at least $1-C/n$: for every set $A$ of at least $n/d$ cells, at least $3m/5$ keys $x$ have at least $c\,d|A|/n$ hashes in $A$ (counted over the indices $i$ with $h_i(x)\in A$), and from the cell of such a key the first step of the walk chooses a hash in $A$ with probability
--   $$\Pr_{i\sim\mathrm{Unif}[d]}\bigl(h_i(x)\in A\bigr)\ge c\,\frac{|A|}{n}.$$
--
--   This shows that the walk enters every large set quickly from most cells.
--
--   Differences from the source:
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - encoding: 'the first step of the walk chooses a hash in A' → the probability, under the probe stream, that h x (ω 0) ∈ A; reason: the walk's first probe index is uniform on [d]
--   - encoding: keys with Ω(d|A|/n) hashes in A → the number of indices i : Fin d with h x i ∈ A (hashes counted with multiplicity) is at least c·d·|A|/n; reason: the proof counts the d independent hashes of a key, a binomial count over indices (p. 27)
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 27 (PDF 28), Lemma 6.6

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk
import Definitions.Def_RWCuckoo_Threshold_Expansion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 6.6, hitting large sets (p. 27): for `d ≥ D0` and `ε∗_d < ε < e^{−d/4}`, w.h.p., for
every set `A` of at least `n/d` cells, at least `3m/5` keys have at least `c d |A|/n` hashes in
`A`, and from the cell of such a key the first step of the walk chooses a hash in `A` with
probability at least `c |A|/n`; `c` absolute. -/
theorem lemma_6_6 :
    ∃ D0 : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε →
      ε < Real.exp (-(d : ℝ) / 4) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ A : Finset (Fin n), (n : ℝ) / d ≤ A.card →
              ∃ X : Finset (Fin (numKeys n ε)), 3 * (numKeys n ε : ℝ) / 5 ≤ X.card ∧
                ∀ x ∈ X,
                  c * d * A.card / n ≤ ((Finset.univ.filter fun i => h x i ∈ A).card : ℝ) ∧
                  ENNReal.ofReal (c * A.card / n) ≤ streamMeasure d {ω | h x (ω 0) ∈ A}} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
