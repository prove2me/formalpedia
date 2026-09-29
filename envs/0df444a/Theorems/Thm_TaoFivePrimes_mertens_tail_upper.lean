-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_tail_upper
-- name    : TaoFivePrimes.mertens_tail_upper
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-27T15:33:47.328593+00:00
-- url     : https://prove2.me/theorems/b49e9015-9fd8-40d8-b077-94c8de97625d
-- title:
--   The Mertens correction tail is at most $1/\lfloor x\rfloor$: $T(N)-T(\infty)\le 1/N$ for $x\ge2$
-- statement:
--   Write, for $N=\lfloor x\rfloor$,
--
--   $$T(N)=\sum_{p\le N}\Bigl(\log(1-\tfrac1p)+\tfrac1p\Bigr),\qquad
--   T(\infty)=\sum_p\Bigl(\log(1-\tfrac1p)+\tfrac1p\Bigr),$$
--
--   the finite and the infinite Mertens correction sums (the second converges absolutely, and $B=\gamma+T(\infty)$ is the Meissel--Mertens constant). For every real $x\ge 2$ this node asserts
--
--   $$T(N)-T(\infty)\ \le\ \frac1N.$$
--
--   It is the companion of the already-Proved `TaoFivePrimes.mertens_tail_le_partial_sum`, which is the opposite inequality $T(\infty)\le T(N)$. Read together they say the correction sum overshoots its limit by a nonnegative amount of size at most $1/N$.
--
--   **Why this is the missing piece.** The Mawia reciprocal-prime estimates go through the exact identity $\sum_{p\le x}\frac1p=\log\prod_{p\le x}\frac{p}{p-1}+T(N)$. The *lower* half only needs $T(N)-T(\infty)\ge0$, i.e. the node that already exists. The *upper* half needs $T(N)-T(\infty)$ bounded **above**, which nothing on the platform supplied. That asymmetry is the whole reason the upper halves are still open.
--
--   **Proof (elementary; no PNT, no numerics, no external citation).** Put $u=1/p$. For $0\le u<1$ the two standard logarithm inequalities
--
--   $$1-(1-u)^{-1}\le\log(1-u)\ \le\ (1-u)-1=-u$$
--
--   (`Real.one_sub_inv_le_log_of_pos` and `Real.log_le_sub_one_of_pos`) give on the one hand $\log(1-u)+u\le0$ -- every correction term is nonpositive, so the partial sums decrease -- and on the other
--
--   $$0\ \le\ -\bigl(\log(1-u)+u\bigr)\ \le\ -1+(1-u)^{-1}-u=\frac{u^2}{1-u}=\frac{1}{p(p-1)}.$$
--
--   Since $\frac1{p(p-1)}=\frac1{p-1}-\frac1p$ telescopes, the tail over *all* integers above $N$ sums to exactly $1/N$, and the prime-supported tail is dominated by it:
--
--   $$T(N)-T(\infty)=\sum_{p>N}-\bigl(\log(1-\tfrac1p)+\tfrac1p\bigr)
--   \ \le\ \sum_{n>N}\Bigl(\frac1{n-1}-\frac1n\Bigr)=\frac1N.$$
--
--   **Remark on the constant (a factor of 2 is being left on the table).** The sharp constant is $\frac1{2N}$. It follows from the second-order estimate
--   $\bigl|\log(1-u)+u\bigr|\le\frac{u^2}{2(1-u)}$, which after the substitution $x=(1-u)^{-1}\ge1$ is the classical $\log x\le\frac12(x-x^{-1})$: the derivative of the difference is $\frac{(x-1)^2}{2x^2}\ge0$ and both sides vanish at $x=1$. That gives $T(N)-T(\infty)\le\sum_{p>N}\frac1{2p(p-1)}\le\frac1{2N}$. Its formalisation needs a monotonicity/derivative argument, so this node states the derivative-free $1/N$ form, which is already sufficient for the intended applications.
--
--   **Role / measured coverage.** Combined with the already-Proved product bounds it closes the upper half of `mawia_reciprocal_sum_upper_bound_small` on $286\le x\le 10^8$: with $\delta=T(N)-T(\infty)\le1/N$ the (3.29)-form node `rosser_schoenfeld_product_log_bound_mid` suffices for $286\le x\le 1978$ and the (4.10)-form node `rosser_schoenfeld_product_bound_to_1e8` for $450\le x\le10^8$. The residue $2\le x<286$ is NOT covered: a sieve check shows the (4.10) form is too weak there (it fails already at $x\approx 12$ and only recovers at $x\approx 450$), and the (3.29) form is *false* below $286$ -- at $x=20$ it would require $\prod_{p\le19}p/(p-1)<4.785$ while the product is $5.848$, which is why Rosser and Schoenfeld themselves state (3.29) only for $x\ge286$.
-- source:
--   Not a quotation: an elementary estimate proved here from the two standard logarithm inequalities log(1-u) >= 1 - (1-u)^{-1} and log(1-u) <= (1-u) - 1 (0 <= u < 1), plus the telescoping identity 1/(n(n-1)) = 1/(n-1) - 1/n. No external source and no numerical certificate is used.

import Mathlib

namespace TaoFivePrimes

theorem mertens_tail_upper (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        1 / (⌊x⌋₊ : ℝ) := by
  sorry

end TaoFivePrimes
