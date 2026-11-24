-- Prove2me | Theorems.Thm_TaoFivePrimes_tao_totient_cert_primorial_nth
-- name    : TaoFivePrimes.tao_totient_cert_primorial_nth
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T20:45:01.264975+00:00
-- url     : https://prove2.me/theorems/886926a5-2fa1-49bf-bbcd-9b682d8d7bd8
-- title:
--   Primorial of the k-th prime as a product of the first k+1 primes
-- statement:
--   Let $p_{k+1}$ be the $(k+1)$-st prime, i.e. $p_{k+1} = \mathrm{Nat.nth}\ \mathrm{Nat.Prime}\ k$. The primorial $\mathrm{primorial}(N)$ is the product of all primes $\le N$. The theorem states that the primorial of the $(k+1)$-st prime is the product of the first $k+1$ primes:
--   $$ \mathrm{primorial}(p_{k+1}) \;=\; \prod_{i=0}^{k} p_{i+1} \;=\; p_1 p_2 \cdots p_{k+1}. $$
--
--   This is the standard identity behind Chebyshev's function $\vartheta(p_{k+1}) = \log \mathrm{primorial}(p_{k+1})$; it converts between the primorial form and the explicit prime-product form, and is the step that lets the finite totient verification evaluate $\vartheta$ at the sample points $p_{k+1}$ through the product of the table entries `ptab`.
-- source:
--   Standard identity for the primorial; in Mathlib it follows from `Nat.primorial_eq_prod_primesLE`. See J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94, Section 3, for the use of $\vartheta(N) = \log \mathrm{primorial}(N)$.

import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Nth

namespace TaoFivePrimes

theorem tao_totient_cert_primorial_nth (k : ℕ) :
    primorial (Nat.nth Nat.Prime k) = ∏ i ∈ Finset.range (k+1), Nat.nth Nat.Prime i := by sorry

end TaoFivePrimes
