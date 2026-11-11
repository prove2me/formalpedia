-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_theorem_1_1
-- name    : RWCuckoo.Threshold.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:34.482511+00:00
-- url     : https://prove2.me/theorems/edb0f0b9-c052-458b-83f0-281568f7231a
-- title:
--   Theorem 1.1 — random-walk cuckoo hashing: E[T^insertion | H_n] ≤ O((d/s)ε⁻¹)(d/s)^{O(1/√(d log d))} and ≤ O((ε − ε∗_d)^{−1−O(1/√(d log d))})
-- statement:
--   Consider $d$-ary cuckoo hashing with $n$ cells: $m=\lfloor(1-\varepsilon)n\rfloor$ keys are inserted by random-walk insertion into an empty table, every key having $d$ independent uniform hashes, and then the $(m+1)$-th key is inserted; $T^{\mathrm{insertion}}\in\mathbb N\cup\{\infty\}$ is its cost (evictions plus one). Let $\varepsilon^*_d$ be the threshold of Fountoulakis and Panagiotou, $s=\ln(\varepsilon/\varepsilon^*_d)$.
--
--   There are absolute constants $D_0$ and $C>0$ such that for every integer $d\ge D_0$ and every $\varepsilon$ with $\varepsilon^*_d<\varepsilon\le1$ there is $n_0(d,\varepsilon)$ such that for every $n\ge n_0$ some hash-only event $H_n$ has $\Pr(H_n^c)\le C/n$ and
--   $$\mathbb E[T^{\mathrm{insertion}}\mid H_n]\le C\,\frac ds\,\varepsilon^{-1}\Bigl(\frac ds\Bigr)^{C/\sqrt{d\log d}}\quad\text{and}\quad \mathbb E[T^{\mathrm{insertion}}\mid H_n]\le C\,(\varepsilon-\varepsilon^*_d)^{-1-C/\sqrt{d\log d}} .$$
--
--   This is the paper's headline result: random-walk insertion is efficient at every load below the critical threshold, with a bound polynomial in $1/(\varepsilon-\varepsilon^*_d)$ and nearly matching the heuristic $O((d/s)\varepsilon^{-1})$.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: random hashes, random probe choices, T^insertion, E[T^insertion | H_n] → uniform measure on Fin (m+1) → Fin d → Fin n times an i.i.d. uniform probe stream ℕ → Fin d consumed in order by all insertions; T^insertion : ℕ∞ (⊤ if an insertion never ends); E[· | H_n] = lintegral of the ℝ≥0∞ coercion against ProbabilityTheory.cond; reason: the probability space the paper describes (pp. 4–5); expectations of an ℕ ∪ {∞}-valued cost live in ℝ≥0∞
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - encoding: ε∗_d the threshold of [FP12] → epsStar d = 1 − ξ_d/(d(1 − e^{−ξ_d})^{d−1}), ξ_d = sup{ξ > 0 : (d − ξ)e^ξ − d − (d − 1)ξ ≥ 0}; reason: the formula the paper prints on p. 41; for d ≥ 3 the sup is the unique positive root
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 2 (PDF 3), Theorem 1.1

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Theorem 1.1 (p. 2): there are absolute constants `D0` and `C > 0` such that for every integer
`d ≥ D0` and every `ε` with `ε∗_d < ε ≤ 1`, for all `n` large in terms of `d` and `ε`, some
hash-only event `H_n` of the `m + 1 = ⌊(1 − ε)n⌋ + 1` keys has `Pr(H_nᶜ) ≤ C/n` and the cost of the
`(m + 1)`-th random-walk insertion satisfies, with `s = ln(ε/ε∗_d)`,
`E[T^insertion | H_n] ≤ C (d/s) ε⁻¹ (d/s)^{C/√(d log d)}` and
`E[T^insertion | H_n] ≤ C (ε − ε∗_d)^{−1 − C/√(d log d)}`. -/
theorem theorem_1_1 :
    ∃ D0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∃ H : Set (Hashes (numKeys n ε + 1) d n),
          hashMeasure (numKeys n ε + 1) d n Hᶜ ≤ ENNReal.ofReal (C / n) ∧
          condExpInsertionTime (numKeys n ε) d n H ≤
            ENNReal.ofReal (C * ((d : ℝ) / sGoal d ε) * ε⁻¹ *
              ((d : ℝ) / sGoal d ε) ^ (C / Real.sqrt (d * Real.log d))) ∧
          condExpInsertionTime (numKeys n ε) d n H ≤
            ENNReal.ofReal (C * epsDelta d ε ^ (-1 - C / Real.sqrt (d * Real.log d))) := by sorry

end RWCuckoo.Threshold
