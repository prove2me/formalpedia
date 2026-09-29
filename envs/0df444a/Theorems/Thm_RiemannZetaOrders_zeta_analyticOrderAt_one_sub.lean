-- Prove2me | Theorems.Thm_RiemannZetaOrders_zeta_analyticOrderAt_one_sub
-- name    : RiemannZetaOrders.zeta_analyticOrderAt_one_sub
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:54:01.713287+00:00
-- url     : https://prove2.me/theorems/e1d21c86-a3e5-4210-9a30-929aa694a194
-- title:
--   The zeros of $\zeta$ are symmetric about the critical line, with multiplicity
-- statement:
--   **Inside the critical strip, $\zeta$ vanishes to the same order at $\rho$ and at $1-\rho$.**
--
--   For every $\rho$ with $0 < \Re\rho < 1$,
--
--   $$\operatorname{ord}_{1-\rho}\,\zeta \;=\; \operatorname{ord}_{\rho}\,\zeta .$$
--
--   This is the functional equation in its sharpest form for zeros. The completed zeta function
--   $\Lambda(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$ satisfies the symmetric identity
--   $\Lambda(s) = \Lambda(1-s)$, so $\operatorname{ord}_{s}\Lambda = \operatorname{ord}_{1-s}\Lambda$
--   trivially. Transferring that to $\zeta$ requires knowing that the archimedean factor
--   $\pi^{-s/2}\Gamma(s/2)$ is holomorphic and non-vanishing at both $\rho$ and $1-\rho$ — which
--   holds because $\Gamma$ has no zeros and its poles lie at $0,-2,-4,\dots$, and because
--   $0 < \Re\rho < 1$ forces $0 < \Re(1-\rho) < 1$ as well, keeping both points inside the strip.
--
--   The statement about **orders**, not merely about vanishing, is what is needed for zero-counting:
--   the Riemann–von Mangoldt formula and every zero-density estimate count zeros with multiplicity,
--   and this identity is what makes the count symmetric under $\rho \mapsto 1-\rho$. The critical
--   line $\Re s = 1/2$ is the fixed-point set of that involution.
--
--   **Formalization note.** `analyticOrderAt` is Mathlib's order of vanishing, valued in
--   $\mathbb{N}\cup\{\infty\}$, so the statement includes the case where $\zeta$ vanishes
--   identically near the point (which does not occur, but need not be excluded).
-- source:
--   Classical; see Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1, and Iwaniec & Kowalski, *Analytic Number Theory*, §5.1. Lean proof extracted from `Salt/SW/BoxFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace RiemannZetaOrders

theorem zeta_analyticOrderAt_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ := by sorry

end RiemannZetaOrders
