-- Prove2me | Theorems.Thm_TaoFivePrimes_siftedVonMangoldt_prime_of_ne_zero
-- name    : TaoFivePrimes.siftedVonMangoldt_prime_of_ne_zero
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-12T16:31:48.793874+00:00
-- url     : https://prove2.me/theorems/f23dcc42-bb05-4334-91e4-5149d1ebe50a
-- title:
--   Below $N$ the sifted von Mangoldt weight is supported on the primes
-- statement:
--   Fix a cutoff $N$ and let
--
--   $$\Lambda^{\sharp}_{N}(n)\;=\;\Lambda(n)\,\mathbf 1_{\gcd(n,\,\lfloor\sqrt N\rfloor^{\sharp})=1}$$
--
--   be the von Mangoldt function with every prime factor up to $\sqrt N$ sifted out, where $m^{\sharp}$ is the primorial of $m$, the product of all primes at most $m$, and $\lfloor\sqrt N\rfloor$ is the integer square root of $N$. This is the weight attached to the prime sums of Section 8 of the source.
--
--   If $n\le N$ and $\Lambda^{\sharp}_{N}(n)\neq0$, then $n$ is prime.
--
--   In other words, below the cutoff the sifted weight sees no proper prime powers: sifting out the primes up to $\sqrt N$ removes every $p^{k}$ with $k\ge2$ that is at most $N$. This is what allows the sums of Section 8 to be read as sums over primes rather than over prime powers, so that a lower bound on the sifted mass produces genuine primes.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 2 (Notation), the sifted von Mangoldt convention Λ_{q_0}(n) = Λ(n) 1_{(n,q_0)=1} with q_0 = (√x)^♯ taken as in Section 8; combined with the elementary Chebyshev bound n^♯ ≤ 4^n of P. Erdős, Beweis eines Satzes von Tschebyschef, Acta Sci. Math. (Szeged) 5 (1932), 194-198, as formalised in Mathlib as primorial_le_four_pow.

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes
open scoped ArithmeticFunction.vonMangoldt

theorem TaoFivePrimes.siftedVonMangoldt_prime_of_ne_zero {N n : ℕ} (hn : n ≤ N)
    (h : TaoFivePrimes.siftedVonMangoldt N n ≠ 0) : n.Prime := by sorry
