-- Prove2me | Theorems.Thm_TaoFivePrimes_rho_certificate
-- name    : TaoFivePrimes.rho_certificate
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-29T13:23:30.85541+00:00
-- url     : https://prove2.me/theorems/47fbcb76-bdfe-4ef6-a0fe-4c16ba8d8e3f
-- title:
--   Error-term reduction for the finite reciprocal-prime endpoint certificate
-- statement:
--   For every integer $2\le n\le 511$, the rational error term
--   $$\rho(n)\,=\,\rho_1(n)+\rho_2(n)$$
--   of the finite endpoint certificate for the reciprocal-prime sum satisfies
--   $$\rho(n)\ \le\ \Bigl(\log\log n-\mathrm{llb}\bigl(\mathrm{lastP}(n)\bigr)\Bigr)
--   +\Bigl(\frac{4}{\log^{3}(n+1)}-\frac{4}{\mathrm{lub}\bigl(\mathrm{firstP}(n)\bigr)^{3}}\Bigr),$$
--   where $\mathrm{lastP}(n)$ is the largest prime $\le n$, $\mathrm{firstP}(n)$ the smallest prime $\ge n$, and the rational tables $\mathrm{llb},\mathrm{lub},\mathrm{clbZ}$ are the log-log table bounds of `TaoFivePrimes_mertens_cert_511_tables`.
--
--   The terms are $\rho_1(n)=\rho_{1f}(\mathrm{lastP}(n),n-\mathrm{lastP}(n))$ with
--   $$\rho_{1f}(m,d)=\frac{\frac{d}{m}-\frac12(\frac{d}{m})^{2}}{\mathrm{lub}(m)}-\frac{(\frac{d}{m})^{2}}{2\,(\mathrm{clbZ}(m)/10^{4})^{2}},$$
--   the second-order Taylor correction obtained by expanding $t\mapsto\log\log t$ between the largest prime below $n$ and $n$, and $\rho_2(n)=\rho_{2f}(\mathrm{firstP}(n),\mathrm{firstP}(n)-n-1)$ with $\rho_{2f}(q,c)=12c/(q\,\mathrm{lub}(q)^{4})$, the corresponding correction towards the smallest prime above $n$ measured against the endpoint terms $4/\log^{3}$.
--
--   This lemma is the analytic heart of the reduction of the endpoint certificate: it converts the rational Taylor-type errors of the finite certificate into the log-log comparison between $n$ and its neighbouring primes, using the table inequalities $\mathrm{llb}(p)\le\log\log p$, $\log p\le\mathrm{lub}(p)$ and $\mathrm{clbZ}(p)/10^{4}\le\log p$.
--
--   **Formalization Note.** The bounds are stated for every integer $2\le n\le 511$; the outermost terms are used at $n+1$ so that the final estimate holds on the whole half-open interval $[n,n+1)$ for real arguments.

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

namespace TaoFivePrimes

theorem rho_certificate (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (rho n : Real) ≤ (Real.log (Real.log (n:Real)) - (llb (lastP n) : Real)) +
      (4/(Real.log ((n:Real)+1))^3 - 4/(lub (firstP n) : Real)^3) := by
  sorry

end TaoFivePrimes
