-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma15_corrected
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_lemma15_corrected
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-17T09:14:04.371951+00:00
-- url     : https://prove2.me/theorems/8f7e6e2d-a25b-4c8e-919a-5fae583a8734
-- title:
--   Rosser–Schoenfeld (1962), Lemma 15 (corrected constant 288)
-- statement:
--   **Rosser--Schoenfeld (1962), Lemma 15.** Let $n > 1$ be an integer and $y$ a real number such that
--   - $288 \le \log n + y$,
--   - $\log n < \theta(\log n + y)$ (so in particular $y > 0$),
--   - $0 \le y - 2$ and $y - 2 \le \dfrac{0.9\, \log n}{\log\log n}$.
--
--   Then
--   $$\frac{n}{\varphi(n)} \;<\; e^{\gamma} \log\log n + \frac{5}{2\log\log n},$$
--   where $\gamma$ is the Euler--Mascheroni constant.
--
--   The constant is $288$: in the proof (p. 89) one first assumes $255 \le \log n \le 1340$, takes $y = 2 + 2\sqrt{1 + \log n}$, giving $288 < \log n + y < 1420$, and applies (3.29) with $x = \log n + y - 2 \ge 286$. (An OCR digitization of the source misreads the constant as "2.88".) This lemma is the analytic core of Theorem 15: it combines Theorem 33, the product estimate (3.29) with $x = \log n + y - 2$, and the numerical bound $2e^{\gamma} < 5/2$.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §9, pp. 88–89, Lemma 15 (constant 288, cf. the displayed chain 288 < log n + y < 1420 on p. 89). https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_totient_lemma15_corrected (n : ℕ) (y : ℝ) (hn : 1 < n)
    (h1 : 288 ≤ Real.log (n : ℝ) + y)
    (h2 : Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y))
    (h3 : 0 ≤ y - 2)
    (h4 : y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        5 / (2 * Real.log (Real.log (n : ℝ))) := by sorry
end TaoFivePrimes
