-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_le
-- name    : TaoFivePrimes.rosser_schoenfeld_psi_le
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T06:54:57.82776+00:00
-- url     : https://prove2.me/theorems/2251aa61-3c72-4174-9f50-0957de1407e8
-- title:
--   Rosser–Schoenfeld upper bound $\psi(x) \le 1.04\,x$ for the Chebyshev function
-- statement:
--   For every real $x > 0$, the Chebyshev function $\psi(x) = \sum_{n \le x} \Lambda(n)$ satisfies
--   $$\psi(x) \;\le\; 1.04\, x.$$
--   This is the Rosser–Schoenfeld theorem $\psi(x) < 1.03883\, x$ (their 1962 Theorem 12), recorded with the slack constant $1.04$ that Tao uses in Lemma 4.3 and in the proof of Proposition 4.10.
-- source:
--   J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94, Theorem 12; used with the slack constant $1.04$ in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Lemma 4.3 and proof of Proposition 4.10.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_psi_le (x : ℝ) (hx : 0 < x) :
    Chebyshev.psi x ≤ 1.04 * x := by sorry

end TaoFivePrimes
