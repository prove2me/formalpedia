-- Prove2me | Theorems.Thm_TaoFivePrimes_endpoint_certificate
-- name    : TaoFivePrimes.endpoint_certificate
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-29T12:53:47.398962+00:00
-- url     : https://prove2.me/theorems/d7a4c14f-caa8-4406-af5a-082fb4686fc6
-- title:
--   510-case endpoint certificate for the reciprocal-prime estimate below 512
-- statement:
--   For every integer $2\le n\le 511$,
--   $$T(n)\ \le\ \mathrm{llb}\bigl(\mathrm{lastP}(n)\bigr)\ +\ \rho(n)\ +\ \frac{4}{\mathrm{lub}\bigl(\mathrm{firstP}(n)\bigr)^{3}}\ +\ M_q ,$$
--   where
--
--   1. $T(n)=\sum_{p\le n}1/p$ is the partial reciprocal-prime sum,
--   2. $\mathrm{lastP}(n)$ is the largest prime $\le n$ and $\mathrm{firstP}(n)$ the smallest prime $\ge n$,
--   3. $\mathrm{llb}$ and $\mathrm{lub}$ are the certified rational lower/upper tables for $\log\log$ and $\log$,
--   4. $\rho(n)=\rho_1(n)+\rho_2(n)$ is the rational endpoint error term built from the tables, and
--   5. $M_q=\frac{32380009}{125000000}$.
--
--   This is the finite 510-case numerical certificate underlying the endpoint estimate: combined with the analytic tail bound it yields, for every integer $2\le n\le 511$, the reciprocal-prime estimate with Meissel-Mertens constant and correction $4/\log^3(n+1)$.
--
--   **Formalization Note.** All quantities on both sides are exact rationals coerced from the tables of `TaoFivePrimes_mertens_cert_511_tables`; the four analytic constants are represented by their displaced rounded values, so the statement is a purely finite arithmetic claim.

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

namespace TaoFivePrimes

theorem endpoint_certificate (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (T n : Rat) ≤ llb (lastP n) + rho n + 4/(lub (firstP n))^3 + Mq := by
  sorry

end TaoFivePrimes
