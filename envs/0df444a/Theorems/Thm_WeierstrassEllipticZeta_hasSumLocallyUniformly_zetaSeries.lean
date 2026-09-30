-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_hasSumLocallyUniformly_zetaSeries
-- name    : WeierstrassEllipticZeta.hasSumLocallyUniformly_zetaSeries
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T00:00:11.952346+00:00
-- url     : https://prove2.me/theorems/87a7e51a-d6b9-4e65-86a1-27494fbdb1a8
-- title:
--   Local uniform convergence of the canonical zeta series
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$. For a nonzero lattice point $\lambda$, write
--   $$a_\lambda(z)=\frac1{z-\lambda}+\frac1\lambda+\frac z{\lambda^2},\qquad a_0(z)=0.$$
--   The finite partial sums converge locally uniformly to their unordered sum:
--   $$\sum_{\lambda\in F}a_\lambda(z)\longrightarrow\sum_{\lambda\in\Omega}a_\lambda(z)\quad(F\uparrow\Omega).$$
--   This supplies convergence of the regularized series in the mission's canonical zeta definition, enabling differentiation on the complement of the lattice.
--
--   **Formalization Note** Division has Lean's totalized values at poles. The local uniform convergence statement also holds at lattice points under that convention, since the finitely many nearby singular summands are eventually present in every partial sum. No continuity at a pole is asserted. The classical analytic interpretation is on $\mathbb C\setminus\Omega$.
-- source:
--   NIST DLMF §23.2(ii), equation 23.2.5 and the convergence paragraph following 23.2.6, https://dlmf.nist.gov/23.2. The statement extends the tail convergence to totalized lattice values; its analytic use remains off the lattice.

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

theorem hasSumLocallyUniformly_zetaSeries (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (fun z ↦ ∑' l : L.lattice, if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by sorry

end WeierstrassEllipticZeta
