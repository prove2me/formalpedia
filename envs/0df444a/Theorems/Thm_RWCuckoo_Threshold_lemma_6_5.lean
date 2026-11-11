-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_6_5
-- name    : RWCuckoo.Threshold.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:33:06.44976+00:00
-- url     : https://prove2.me/theorems/7d499d9b-1765-496a-a7bd-4ab5a985d4e9
-- title:
--   Lemma 6.5 — the expansion loss of every retained group is O((d/s)^{O(1/√(d log d))})
-- statement:
--   Let $d\ge D_0$ and let $\varepsilon$ satisfy (13), $e^{-d}+e^{-5d/4}\le\varepsilon<e^{-d/4}$ (and $\varepsilon>\varepsilon^*_d$); write $s=d-\log(1/\varepsilon)$. There is an absolute $C$ such that for all large $n$, with probability at least $1-C/n$: for every admissible configuration $(M,F)$ with $|F|\ge sm/8$ and every retained group $j$, the sets $S_i=N^i(S_0)$, $S_0=S^{(j)}_0$, reach size $n/d$, i.e. $H=\min\{i\ge0:|S_i|\ge n/d\}$ is finite, and
--   $$\frac{d^H|S_0|}{|S_H|}\le C\Bigl(\frac ds\Bigr)^{C/\sqrt{d\log d}} .$$
--
--   The expansion loss controls how likely the walk is to reach the fresh probes of a group by following the sets $S_i$ backwards.
--
--   Differences from the source:
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - encoding: admissible configuration (M, F): output of an adversary (Definition 5.2) → IsAdmissible M F: no matching probe (x, idx x) lies in F; reason: for given hashes these are exactly the pairs some adversary can output (examine the complement of F, output M)
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - encoding: H = min{i ≥ 0 : |S_i| ≥ n/d} is finite → ∃ H with |S_H| ≥ n/d and |S_i| < n/d for all i < H, and the loss bound at that H; reason: the first index, stated without Nat.find
--   - encoding: retained group j (weight 2^j|S^(j)_0| at least a 1/(2L) fraction of the total weight), S_0 = S^(j)_0 → IsRetained M F j: group j nonempty and total weight ≤ 2L·2^j|S^(j)_0|, with the total weight and L summed over j ≤ d; S_0 = groupCells M F j; reason: groups j > d are empty; nonemptiness only excludes total weight 0, which |F| ≥ sm/8 > 0 rules out; designating 2^j probes per cell does not change S_0
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 26 (PDF 27), Lemma 6.5

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk
import Definitions.Def_RWCuckoo_Threshold_Expansion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 6.5, expansion loss (p. 26): for `d ≥ D0` and `ε` in the range (13),
`e^{−d} + e^{−5d/4} ≤ ε < e^{−d/4}` (with `ε > ε∗_d`), and `s = d − log(1/ε)`: w.h.p., for every
admissible configuration `(M, F)` with `|F| ≥ sm/8` and every retained group `j`, the sets
`S_i = N^i(S_0)`, `S_0 = S^(j)_0`, reach size `n/d` at a first index `H`, and
`d^H |S_0| / |S_H| ≤ C (d/s)^{C/√(d log d)}`. -/
theorem lemma_6_5 :
    ∃ D0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε →
      Real.exp (-(d : ℝ)) + Real.exp (-5 * (d : ℝ) / 4) ≤ ε → ε < Real.exp (-(d : ℝ) / 4) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ (M : Matching h) (F : Finset (Fin (numKeys n ε) × Fin d)), IsAdmissible M F →
              sFresh d ε * numKeys n ε / 8 ≤ F.card → ∀ j : ℕ, IsRetained M F j →
              ∃ H : ℕ, (n : ℝ) / d ≤ (M.nbhdIter H (groupCells M F j)).card ∧
                (∀ i < H, ((M.nbhdIter i (groupCells M F j)).card : ℝ) < n / d) ∧
                (d : ℝ) ^ H * (groupCells M F j).card / (M.nbhdIter H (groupCells M F j)).card ≤
                  C * ((d : ℝ) / sFresh d ε) ^ (C / Real.sqrt (d * Real.log d))} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
