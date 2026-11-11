-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_theorem_7_1
-- name    : RWCuckoo.Threshold.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:19.483448+00:00
-- url     : https://prove2.me/theorems/678635b7-b87f-4518-8944-e3187842dec0
-- title:
--   Theorem 7.1 — every ε > ε∗_d: E[T^insertion | H_n] = O(ε_Δ^{−1−O(1/√(d log d))}), and for ε < e^{−d/4} also E T^frozen ≤ ε_Δ^{−1−O(1/√(d log d))} for every matching
-- statement:
--   There are absolute constants $D_0$ and $C>0$ such that for $d\ge D_0$ and $\varepsilon^*_d<\varepsilon\le1$ there is a threshold $n_0(d,\varepsilon)$ such that for every $n\ge n_0$:
--
--   1. there is a hash-only event $H_n$ with $\Pr(H_n^c)\le C/n$ and $\mathbb E[T^{\mathrm{insertion}}\mid H_n]\le C\,\varepsilon_\Delta^{-1-C/\sqrt{d\log d}}$;
--   2. if moreover $\varepsilon<e^{-d/4}$, then with probability at least $1-C/n$, every matching satisfies
--   $$\mathbb E\,T^{\mathrm{frozen}}\le\varepsilon_\Delta^{-1-C/\sqrt{d\log d}} .\tag{16}$$
--
--   This covers the regime closest to the threshold, $\varepsilon<e^{-d}+e^{-5d/4}$, by growing sets backwards from the empty cells.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: random hashes, random probe choices, T^insertion, E[T^insertion | H_n] → uniform measure on Fin (m+1) → Fin d → Fin n times an i.i.d. uniform probe stream ℕ → Fin d consumed in order by all insertions; T^insertion : ℕ∞ (⊤ if an insertion never ends); E[· | H_n] = lintegral of the ℝ≥0∞ coercion against ProbabilityTheory.cond; reason: the probability space the paper describes (pp. 4–5); expectations of an ℕ ∪ {∞}-valued cost live in ℝ≥0∞
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - encoding: E T^frozen, E T^fresh, E N_G (expectation over the walk, for fixed hashes and matching) → lintegral in ℝ≥0∞ of the ℕ∞-valued walk length or visit count against the uniform first cell × an i.i.d. uniform probe stream ℕ → Fin d (⊤ if the walk never stops); reason: the walk randomness of Definitions 2.1 and 5.3; expectations of possibly infinite lengths live in ℝ≥0∞
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 29 (PDF 30), Theorem 7.1

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Theorem 7.1 (p. 29): for `d ≥ D0` and `ε∗_d < ε ≤ 1`, for all `n ≥ n0(d, ε)`: there are hash-only
events `H_n` with `Pr(H_nᶜ) ≤ C/n` and `E[T^insertion | H_n] ≤ C ε_Δ^{−1 − C/√(d log d)}`; and if
moreover `ε < e^{−d/4}`, then with probability at least `1 − C/n`, every matching has
`E T^frozen ≤ ε_Δ^{−1 − C/√(d log d)}` (16). `D0`, `C` absolute. -/
theorem theorem_7_1 :
    ∃ D0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        (∃ H : Set (Hashes (numKeys n ε + 1) d n),
          hashMeasure (numKeys n ε + 1) d n Hᶜ ≤ ENNReal.ofReal (C / n) ∧
          condExpInsertionTime (numKeys n ε) d n H ≤
            ENNReal.ofReal (C * epsDelta d ε ^ (-1 - C / Real.sqrt (d * Real.log d)))) ∧
        (ε < Real.exp (-(d : ℝ) / 4) →
          hashMeasure (numKeys n ε) d n
              {h | ¬ ∀ M : Matching h,
                expFrozenTime M ≤
                  ENNReal.ofReal (epsDelta d ε ^ (-1 - C / Real.sqrt (d * Real.log d)))} ≤
            ENNReal.ofReal (C / n)) := by sorry

end RWCuckoo.Threshold
