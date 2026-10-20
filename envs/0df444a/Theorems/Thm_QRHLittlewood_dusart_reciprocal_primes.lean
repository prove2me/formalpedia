-- Prove2me | Theorems.Thm_QRHLittlewood_dusart_reciprocal_primes
-- name    : QRHLittlewood.dusart_reciprocal_primes
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:35:07.641621+00:00
-- url     : https://prove2.me/theorems/7a9cd00f-d5f7-4cea-b215-e0977a43a746
-- title:
--   Dusart's explicit upper bound for $\sum_{p\le x}1/p$
-- statement:
--   Let $\gamma$ be the Euler–Mascheroni constant and let
--
--   $$B=\gamma+\sum_{p}\Big(\log\Big(1-\frac1p\Big)+\frac1p\Big)$$
--
--   be Mertens' constant, the sum running over all primes. For every real $x\ge10372$,
--
--   $$\sum_{p\le x}\frac1p-\log\log x-B\ \le\ \frac{1}{10\log^2x}+\frac{4}{15\log^3x}.$$
--
--   This is the explicit form of Mertens' second theorem used to bound smoothed sums over primes.
--
--   **Status note (2026-10-17)** The release [Dusart v2.0.0, doi:10.5281/zenodo.23432990](https://doi.org/10.5281/zenodo.23432990) proves this bound in Lean 4 from the Chebyshev estimate for $t\ge3584912846=\lfloor e^{22}\rfloor$ alone (`Dusart.dusart_reciprocal_primes_of_chebyshev_large`).
--
--   **Status note (2026-10-19)** The release [Dusart v3.0.0, doi:10.5281/zenodo.23463154](https://doi.org/10.5281/zenodo.23463154) proves this bound in Lean 4 with a single published table row as the only hypothesis, $|\theta(t)-t|<0.15952\,t/\log^2t$ for $t>5\cdot10^6$ (Broadbent, Kadiri, Lumley, Ng and Wilk, Math. Comp. 90 (2021), Theorem 1 with $k=2$, Table 15, row $\log X_0=\log(5\cdot10^6)$) (`Dusart.dusart_reciprocal_primes_of_bklnw`; axioms `propext`, `Classical.choice`, `Quot.sound` only). With that published theorem the bound holds unconditionally as mathematics; the row itself is not formalized, so on this platform the entry stays reduced to the Chebyshev estimate.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound).

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Real

namespace QRHLittlewood

theorem dusart_reciprocal_primes (x : ℝ) (hx : 10372 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) := by sorry

end QRHLittlewood
