-- Prove2me | Theorems.Thm_RiemannZetaOrders_zeta_fe_factor_ne_zero
-- name    : RiemannZetaOrders.zeta_fe_factor_ne_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:47:13.108714+00:00
-- url     : https://prove2.me/theorems/be7aeb45-5999-4fb5-9bce-9157d305b6bd
-- title:
--   The zeta functional-equation factor is non-zero in the critical strip
-- statement:
--   **The archimedean factor in the asymmetric functional equation has no zeros in the strip.**
--
--   Riemann's functional equation in asymmetric form reads
--
--   $$\zeta(s) \;=\; 2\,(2\pi)^{\,s-1}\,\Gamma(1-s)\,\sin\!\left(\frac{\pi s}{2}\right)\zeta(1-s),$$
--
--   and the factor appearing here, $2(2\pi)^{-\rho}\Gamma(\rho)\cos(\pi\rho/2)$, is its companion.
--   For $0 < \Re\rho < 1$ this factor is **never zero**.
--
--   Each of the three parts is separately non-vanishing on the strip:
--
--   * $(2\pi)^{-\rho} = e^{-\rho\log 2\pi}$ is an exponential, hence never zero;
--   * $\Gamma$ has **no zeros anywhere**, by the reflection formula
--     $\Gamma(z)\Gamma(1-z) = \pi/\sin(\pi z)$, and its poles at $0,-1,-2,\dots$ are excluded by
--     $\Re\rho > 0$;
--   * $\cos(\pi\rho/2)$ vanishes only at odd integers $\rho$, all of which have $\Re\rho \ge 1$ or
--     $\Re\rho \le -1$ and so lie outside the strip.
--
--   The consequence is that the functional equation transports zeros **exactly**: within the
--   critical strip, $\zeta(\rho) = 0$ if and only if $\zeta(1-\rho) = 0$, with matching
--   multiplicities. Every reflection argument about the zeros of $\zeta$ — the symmetry of the
--   zero set about the critical line, zero-counting via the argument principle — rests on this
--   non-vanishing.
--
--   **Formalization note.** `Gamma` and `cos` are the complex-analytic versions; the strip
--   hypothesis is given as $0 < \Re\rho < 1$.
-- source:
--   Classical; see Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1. Lean proof extracted from `Salt/SW/BoxFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace RiemannZetaOrders

open Complex in
theorem zeta_fe_factor_ne_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    2 * (2 * (Real.pi : ℂ)) ^ (-ρ) * Gamma ρ * cos ((Real.pi : ℂ) * ρ / 2) ≠ 0 := by sorry

end RiemannZetaOrders
