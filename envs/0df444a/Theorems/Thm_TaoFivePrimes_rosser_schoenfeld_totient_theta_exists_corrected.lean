-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_theta_exists_corrected
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_theta_exists_corrected
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T09:18:30.689276+00:00
-- url     : https://prove2.me/theorems/5991b129-a1bc-4500-9028-b65e451e9c16
-- title:
--   Rosser–Schoenfeld (1962), §9: existence of the Lemma 15 parameter (corrected constant 288)
-- statement:
--   **Rosser--Schoenfeld (1962), §9 (corrected constant).** For every integer $n \ge 3$ with $\log n \ge 294$ there exists a real number $y$ such that
--   $$288 \le \log n + y, \qquad \log n < \theta(\log n + y), \qquad 0 \le y - 2 \le \frac{0.9\,\log n}{\log\log n},$$
--   i.e. $y$ satisfies all the hypotheses of Lemma 15 (apart from $n > 1$, which follows from $n \ge 3$).
--
--   This is the existence statement used in §9, p. 89, to feed Lemma 15: on the range $255 \le \log n \le 1340$ one takes $y = 2 + 2\sqrt{1+\log n}$ and uses Theorem 19 ($\theta(t) > t - 2\sqrt t$) to get $\log n < \theta(\log n+y)$; on $\log n \ge 1340$ one takes $y = 2 + 0.9\log n/\log\log n$ and uses inequality (3.14) ($\theta(t) > t(1 - 1/(2\log t))$). In the first range $\log n + y \ge 255 + 2\sqrt{256} = 289$, and in the second $\log n \ge 1340$, so the displayed lower bound $288 \le \log n + y$ holds in both cases. (Some OCR digitizations misread the printed constant $288$ as "2.88".)
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §9, p. 89 (constant 288; cf. Theorem 19 and inequality (3.14)). https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_totient_theta_exists_corrected (n : ℕ) (hn : 3 ≤ n)
    (hlog : 294 ≤ Real.log (n : ℝ)) :
    ∃ y : ℝ, 288 ≤ Real.log (n : ℝ) + y ∧
      Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y) ∧
      0 ≤ y - 2 ∧ y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := by sorry
end TaoFivePrimes
