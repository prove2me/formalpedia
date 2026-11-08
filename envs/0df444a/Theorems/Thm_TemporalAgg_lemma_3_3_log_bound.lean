-- Prove2me | Theorems.Thm_TemporalAgg_lemma_3_3_log_bound
-- name    : TemporalAgg.lemma_3_3_log_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T21:37:21.133025+00:00
-- url     : https://prove2.me/theorems/3cc70093-2857-4100-99cc-18b36eca58ef
-- title:
--   Proof of Lemma 3.3, p.17 — −log_{3/2}(k/(k−1)) ≥ −(1/ln(3/2))·1/(k−1) ≥ −5/k
-- statement:
--   For every integer $k\ge2$:
--
--   1. $-\log_{3/2}\dfrac{k}{k-1}\ \ge\ -\dfrac{1}{\ln(3/2)}\cdot\dfrac{1}{k-1}$;
--   2. $-\dfrac{1}{\ln(3/2)}\cdot\dfrac{1}{k-1}\ \ge\ -\dfrac{5}{k}$;
--   3. $\ln\dfrac{k}{k-1}\le\dfrac{1}{k-1}$;
--   4. $\dfrac{1}{k-1}\le\dfrac{2}{k}$;
--   5. $\dfrac{1}{\ln(3/2)}<2.5$.
--
--   When the adversary samples another member of a group of size $k\ge2$, the potential term $\log_{3/2}|\mathrm{group}(u)|$ of every other member drops by $\log_{3/2}\frac{k}{k-1}$; this estimate shows the drop is paid by the $5/k$ coins each member receives.
--
--   **Formalization Note** $k$ is cast to $\mathbb R$ before $k-1$ is formed.
--
--   Differences from the source: none.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), proof of Lemma 3.3, p.17

import Mathlib

namespace TemporalAgg

/-- **The logarithmic estimate in the proof of Lemma 3.3** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive
Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.17: "The first term changes
by −log_{3/2} k/(k−1) ≥ −1/ln(3/2) · 1/(k−1) ≥ −5/k, using ln k/(k−1) ≤ 1/(k−1) ≤ 2/k and
1/ln(3/2) < 2.5.").

For every integer `k ≥ 2` (the size of the group, "whose size was k ≥ 2"):
1. `−log_{3/2}(k/(k−1)) ≥ −(1/ln(3/2))·(1/(k−1))`;
2. `−(1/ln(3/2))·(1/(k−1)) ≥ −5/k`;
3. `ln(k/(k−1)) ≤ 1/(k−1)`;
4. `1/(k−1) ≤ 2/k`;
5. `1/ln(3/2) < 2.5`.

**Formalization Note** `k` is cast to `ℝ` before the subtraction `k − 1`; `ln` is
`Real.log` and `log_{3/2}` is `Real.logb (3/2)`. -/
theorem lemma_3_3_log_bound (k : ℕ) (hk : 2 ≤ k) :
    -Real.logb (3 / 2) ((k : ℝ) / ((k : ℝ) - 1)) ≥
        -(1 / Real.log (3 / 2)) * (1 / ((k : ℝ) - 1)) ∧
      -(1 / Real.log (3 / 2)) * (1 / ((k : ℝ) - 1)) ≥ -5 / (k : ℝ) ∧
      Real.log ((k : ℝ) / ((k : ℝ) - 1)) ≤ 1 / ((k : ℝ) - 1) ∧
      1 / ((k : ℝ) - 1) ≤ 2 / (k : ℝ) ∧
      1 / Real.log (3 / 2) < 2.5 := by sorry

end TemporalAgg
