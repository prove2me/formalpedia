-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_5_5
-- name    : RWCuckoo.Threshold.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:27.816782+00:00
-- url     : https://prove2.me/theorems/ea90bcb3-7dbd-4fed-bdc5-707a9f4348c8
-- title:
--   Lemma 5.5 — the first m insertions leave at least dm − n log(1/ε) − δn fresh probes
-- statement:
--   Let $0<\varepsilon\le1$ and $\delta>0$. There are $c>0$ and $n_0$, depending only on $\varepsilon$ and $\delta$, such that for every $d$ and every $n\ge n_0$, with $m=\lfloor(1-\varepsilon)n\rfloor$,
--   $$\Pr\Bigl(\text{the first $m$ insertions all finish and leave fewer than } dm-n\log\tfrac1\varepsilon-\delta n \text{ fresh probes}\Bigr)\le e^{-cn}.$$
--   The probability is over the hashes and the probe choices.
--
--   This counts how fast insertions consume fresh probes: about $n\log(1/\varepsilon)$ of the $dm$ probes are used, the rest stay fresh.
--
--   Differences from the source:
--   - generalization: standing assumptions d ≥ D0 and ε > ε∗_d (§5) → every d and every 0 < ε ≤ 1; reason: the count of fresh probes used is a coupon-collector variable whose law does not involve d or the threshold; the statement for all d, ε specializes to the paper's
--   - encoding: except with probability e^{−Ω_{ε,δ}(n)} → ∃ c > 0, ∃ n0 (both depending on ε, δ only), ∀ d, ∀ n ≥ n0, probability ≤ exp(−c n); reason: the paper's subscript notation for the hidden constant
--   - encoding: random hashes, random probe choices, T^insertion, E[T^insertion | H_n] → uniform measure on Fin (m+1) → Fin d → Fin n times an i.i.d. uniform probe stream ℕ → Fin d consumed in order by all insertions; T^insertion : ℕ∞ (⊤ if an insertion never ends); E[· | H_n] = lintegral of the ℝ≥0∞ coercion against ProbabilityTheory.cond; reason: the probability space the paper describes (pp. 4–5); expectations of an ℕ ∪ {∞}-valued cost live in ℝ≥0∞
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 18 (PDF 19), Lemma 5.5

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 5.5 (p. 18): for every fixed `δ > 0`, except with probability `e^{−Ω_{ε,δ}(n)}`, if the
first `m` insertions all finish then they leave at least `dm − n log(1/ε) − δn` fresh probes. The
rate `c` and the threshold `n0` depend only on `ε` and `δ`. -/
theorem lemma_5_5 :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, ∀ d n : ℕ, n0 ≤ n →
      processMeasure (numKeys n ε + 1) d n
          {p | firstInsertionsFinish p.1 p.2 ∧
            (freshLeft p.1 p.2 : ℝ) < (d : ℝ) * numKeys n ε - n * Real.log (1 / ε) - δ * n} ≤
        ENNReal.ofReal (Real.exp (-(c * n))) := by sorry

end RWCuckoo.Threshold
