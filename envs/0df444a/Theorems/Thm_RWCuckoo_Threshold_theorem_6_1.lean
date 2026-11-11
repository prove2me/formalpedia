-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_theorem_6_1
-- name    : RWCuckoo.Threshold.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:22.124821+00:00
-- url     : https://prove2.me/theorems/cee83ab7-0337-4a5a-84a1-ef6e3d4bf74c
-- title:
--   Theorem 6.1 — small ε in (13): E[T^insertion | H_n] = O(d/(sε))·(d/s)^{O(1/√(d log d))}
-- statement:
--   There are absolute constants $D_0$ and $C>0$ such that for $d\ge D_0$ and $\varepsilon$ with $\varepsilon>\varepsilon^*_d$ and (13), $e^{-d}+e^{-5d/4}\le\varepsilon<e^{-d/4}$, writing $s=d-\log(1/\varepsilon)$, there is a threshold $n_0(d,\varepsilon)$ and, for every $n\ge n_0$, a hash-only event $H_n$ with $\Pr(H_n^c)\le C/n$ and
--   $$\mathbb E[T^{\mathrm{insertion}}\mid H_n]\le C\,\frac{d}{s\varepsilon}\Bigl(\frac ds\Bigr)^{C/\sqrt{d\log d}} .$$
--
--   This proves Theorem 1.1 in the range (13), since $\varepsilon^*_d\ge e^{-d}$ makes this $s$ at least the $s=\ln(\varepsilon/\varepsilon^*_d)$ of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: random hashes, random probe choices, T^insertion, E[T^insertion | H_n] → uniform measure on Fin (m+1) → Fin d → Fin n times an i.i.d. uniform probe stream ℕ → Fin d consumed in order by all insertions; T^insertion : ℕ∞ (⊤ if an insertion never ends); E[· | H_n] = lintegral of the ℝ≥0∞ coercion against ProbabilityTheory.cond; reason: the probability space the paper describes (pp. 4–5); expectations of an ℕ ∪ {∞}-valued cost live in ℝ≥0∞
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 22 (PDF 23), Theorem 6.1

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Theorem 6.1 (p. 22): for `d ≥ D0` and `ε` in the range (13), `e^{−d} + e^{−5d/4} ≤ ε < e^{−d/4}`
(with `ε > ε∗_d`), and `s = d − log(1/ε)`: for all `n ≥ n0(d, ε)` there are hash-only events `H_n`
with `Pr(H_nᶜ) ≤ C/n` and `E[T^insertion | H_n] ≤ C (d/(sε)) (d/s)^{C/√(d log d)}`. -/
theorem theorem_6_1 :
    ∃ D0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε →
      Real.exp (-(d : ℝ)) + Real.exp (-5 * (d : ℝ) / 4) ≤ ε → ε < Real.exp (-(d : ℝ) / 4) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∃ H : Set (Hashes (numKeys n ε + 1) d n),
          hashMeasure (numKeys n ε + 1) d n Hᶜ ≤ ENNReal.ofReal (C / n) ∧
          condExpInsertionTime (numKeys n ε) d n H ≤
            ENNReal.ofReal (C * ((d : ℝ) / (sFresh d ε * ε)) *
              ((d : ℝ) / sFresh d ε) ^ (C / Real.sqrt (d * Real.log d))) := by sorry

end RWCuckoo.Threshold
