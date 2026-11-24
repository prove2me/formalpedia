-- Prove2me | Theorems.Thm_TaoFivePrimes_llb_le_loglog
-- name    : TaoFivePrimes.llb_le_loglog
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-29T12:53:25.991986+00:00
-- url     : https://prove2.me/theorems/928bf346-a437-44f0-bbf7-e77a8e07aed8
-- title:
--   Log-log lower table bound for primes up to 521
-- statement:
--   For each of the 98 primes $p\le 521$, the rational value $\mathrm{llb}(p)$ stored in the lookup table `llb` is a lower bound for the double logarithm of $p$:
--   $$\mathrm{llb}(p)\ \le\ \log\log p .$$
--
--   The value $\mathrm{llb}(p)$ is the rounded-down rational approximation of $\log\log p$ recorded for the prime $p$ in the finite tables of `TaoFivePrimes_mertens_cert_511_tables`. This prime-by-prime inequality is one of the two "log-log sandwich" table obligations used to control the endpoint error term $\rho_1$ in the finite endpoint certificate for the reciprocal-prime estimate.
--
--   **Formalization Note.** The hypothesis $hp : p \in \mathrm{pl521}$ restricts $p$ to the explicit finite set of primes $\le 521$; the statement is a finite table verification.

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

namespace TaoFivePrimes

theorem llb_le_loglog (p : Nat) (hp : p ∈ pl521) :
    (llb p : Real) ≤ Real.log (Real.log (p : Real)) := by
  sorry

end TaoFivePrimes
