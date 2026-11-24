-- Prove2me | Theorems.Thm_TaoFivePrimes_clbZ_table_bounds
-- name    : TaoFivePrimes.clbZ_table_bounds
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-29T12:53:52.051889+00:00
-- url     : https://prove2.me/theorems/f6063143-ef6d-41b9-b064-8830d774582d
-- title:
--   Certified lower logarithm bounds for primes up to 521
-- statement:
--   For every prime $p\le 521$, the integer table value $\mathrm{clbZ}(p)$ of `Definitions.Def_TaoFivePrimes_theta_cert_tables` is positive and certifies a lower bound for the logarithm of $p$ at scale $10^{-4}$:
--   $$0\ <\ \mathrm{clbZ}(p)\qquad\text{and}\qquad \frac{\mathrm{clbZ}(p)}{10^{4}}\ \le\ \log p .$$
--
--   Equivalently, $\mathrm{clbZ}(p)/10^4$ is a certified rational lower approximation of $\log p$. These two facts are the numerical input used for the prime denominator $q=\mathrm{lastP}(n)$ in the error term $\rho_1$ of the finite endpoint certificate for the reciprocal-prime estimate.
--
--   **Formalization Note.** The hypothesis $hp : p \in \mathrm{pl521}$ restricts $p$ to the explicit finite set of primes $\le 521$; positivity is recorded over $\mathbb{N}$ and the bound is stated after coercion to $\mathbb{R}$.

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes

theorem clbZ_table_bounds (p : Nat) (hp : p ∈ pl521) :
    0 < clbZ p ∧ ((clbZ p : Nat) : Real)/10000 ≤ Real.log (p : Real) := by
  sorry

end TaoFivePrimes
