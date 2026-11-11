-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_6_7
-- name    : RWCuckoo.Threshold.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:33:32.574568+00:00
-- url     : https://prove2.me/theorems/90fcfaeb-ae9c-4265-b0de-51dcd7a319bf
-- title:
--   Lemma 6.7 — fresh-stopped walk length O(d/s)·(d/s)^{O(1/√(d log d))} when |F| ≥ sm/8
-- statement:
--   Let $d\ge D_0$ and let $\varepsilon$ satisfy (13), $e^{-d}+e^{-5d/4}\le\varepsilon<e^{-d/4}$ (and $\varepsilon>\varepsilon^*_d$); write $s=d-\log(1/\varepsilon)$. There is an absolute $C$ such that for all large $n$, with probability at least $1-C/n$, every admissible configuration $(M,F)$ with $|F|\ge sm/8$ satisfies
--   $$\mathbb E\,T^{\mathrm{fresh}}\le C\,\frac ds\cdot\Bigl(\frac ds\Bigr)^{C/\sqrt{d\log d}} .\tag{15}$$
--
--   With the restart lemma this gives Theorem 6.1.
--
--   Differences from the source:
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - encoding: admissible configuration (M, F): output of an adversary (Definition 5.2) → IsAdmissible M F: no matching probe (x, idx x) lies in F; reason: for given hashes these are exactly the pairs some adversary can output (examine the complement of F, output M)
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - encoding: E T^frozen, E T^fresh, E N_G (expectation over the walk, for fixed hashes and matching) → lintegral in ℝ≥0∞ of the ℕ∞-valued walk length or visit count against the uniform first cell × an i.i.d. uniform probe stream ℕ → Fin d (⊤ if the walk never stops); reason: the walk randomness of Definitions 2.1 and 5.3; expectations of possibly infinite lengths live in ℝ≥0∞
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 27 (PDF 28), Lemma 6.7

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk
import Definitions.Def_RWCuckoo_Threshold_Expansion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 6.7, fresh-stopped walk (p. 27): for `d ≥ D0` and `ε` in the range (13), with
`s = d − log(1/ε)`: w.h.p., every admissible configuration `(M, F)` with `|F| ≥ sm/8` satisfies
`E T^fresh ≤ C (d/s) (d/s)^{C/√(d log d)}`, `C` absolute. -/
theorem lemma_6_7 :
    ∃ D0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε →
      Real.exp (-(d : ℝ)) + Real.exp (-5 * (d : ℝ) / 4) ≤ ε → ε < Real.exp (-(d : ℝ) / 4) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ (M : Matching h) (F : Finset (Fin (numKeys n ε) × Fin d)), IsAdmissible M F →
              sFresh d ε * numKeys n ε / 8 ≤ F.card →
              expFreshTime M F ≤
                ENNReal.ofReal (C * ((d : ℝ) / sFresh d ε) *
                  ((d : ℝ) / sFresh d ε) ^ (C / Real.sqrt (d * Real.log d)))} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
