-- Prove2me | Theorems.Thm_TaoFivePrimes_constant_certificate
-- name    : TaoFivePrimes.constant_certificate
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-29T13:23:39.8162+00:00
-- url     : https://prove2.me/theorems/7e33e839-ad3a-4c81-85cf-56331a282519
-- title:
--   Absorption of the rounded constant of the finite reciprocal-prime certificate
-- statement:
--   The rounded constant
--   $$M_q=\frac{32380009}{125000000}$$
--   of the finite certificate is bounded by the Euler–Mascheroni constant plus the convergent Meissel–Mertens tail:
--   $$M_q\ \le\ \gamma\ +\ \sum_{p}\Bigl(\log\Bigl(1-\frac1p\Bigr)+\frac1p\Bigr).$$
--
--   The proof decomposes the constant into the table quantities of `TaoFivePrimes_mertens_cert_511_tables`: first $M_q\le M\le \mathrm{glo}+\mathrm{tlo}$ by exact rational arithmetic, where
--   $$\mathrm{glo}=\frac{300367}{40000}-10\cdot\frac{6931471808}{10^{10}}-\frac1{1024},\qquad \mathrm{tlo}=WLO(512)-\frac12\Bigl(\frac1{512}-\frac1{8192}\Bigr)-\frac1{8192}.$$
--   The lower bound $\mathrm{glo}\le\gamma$ follows from the Mathlib bound on the Euler–Mascheroni sequence at index $1024$. The lower bound $\mathrm{tlo}\le\sum_{p}(\log(1-1/p)+1/p)$ is obtained by splitting the tail into three ranges: the finite part over primes $\le 512$ is bounded below by the tabulated sum $WLO(512)$, the middle range $512<p\le 8192$ by the elementary estimate $-\frac12(\frac1{512}-\frac1{8192})\le\sum_{512<p\le 8192}(\log(1-1/p)+1/p)$, and the remaining tail is the platform theorem `TaoFivePrimes.mertens_tail_upper_bound`.
--
--   Together with the endpoint certificate for the table $T$, this constant absorption is what turns the rational constant $M_q$ in the finite certificate into the standard analytic constant $\gamma+\sum_p(\log(1-1/p)+1/p)$ of the reciprocal-prime endpoint estimate.

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

namespace TaoFivePrimes

theorem constant_certificate :
    (Mq : Real) ≤ Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : Real)) + 1 / (p : Real)) := by
  sorry

end TaoFivePrimes
