-- Prove2me | Theorems.Thm_TaoFivePrimes_WLO512_le_sum512
-- name    : TaoFivePrimes.WLO512_le_sum512
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-29T12:53:42.41182+00:00
-- url     : https://prove2.me/theorems/c252993b-c59b-482a-97a5-6064e55d504f
-- title:
--   Rational lower bound for the Meissel-Mertens summand below 512
-- statement:
--   Write $\mathrm{wlo}(p)=\log\bigl(1-\tfrac1p\bigr)+\tfrac1p$ for the summand of the Meissel-Mertens constant and let
--   $$WLO(512)=\sum_{p\le 512}\mathrm{wlo}(p)$$
--   be the value tabulated in `TaoFivePrimes_mertens_cert_511_tables` at rational scale $10^{-9}$. Then
--   $$WLO(512)\ \le\ \sum_{p\le 512}\Bigl(\log\Bigl(1-\frac1p\Bigr)+\frac1p\Bigr),$$
--   i.e. the rounded table value is a lower bound for the true sum over the 97 primes $\le 512$.
--
--   This is the quantitative input that places the tail constant $tlo = WLO(512)-\tfrac12\bigl(\tfrac1{512}-\tfrac1{8192}\bigr)-\tfrac1{8192}$ below the true tail $\sum_{p}(\log(1-1/p)+1/p)$ in the finite endpoint certificate.
--
--   **Formalization Note.** `WLO` is the integer table divided by $10^{9}$; the right-hand side sums over `Nat.primesLE 512`. The statement is a finite table comparison.

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

namespace TaoFivePrimes

theorem WLO512_le_sum512 :
    (WLO 512 : Real) ≤ ∑ p ∈ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
  sorry

end TaoFivePrimes
