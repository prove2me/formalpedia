-- Prove2me | Theorems.Thm_RiemannZetaOrders_completed_order_one_sub
-- name    : RiemannZetaOrders.completed_order_one_sub
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:51.999278+00:00
-- url     : https://prove2.me/theorems/df305304-a27b-4a10-b53a-b7c5fc843ae5
-- title:
--   The completed zeta has symmetric vanishing orders
-- statement:
--   **The completed zeta function vanishes to the same order at $\rho$ and $1-\rho$, everywhere.**
--
--   For every $\rho \in \mathbb{C}$,
--
--   $$\operatorname{ord}_{1-\rho}\Lambda \;=\; \operatorname{ord}_{\rho}\Lambda ,$$
--
--   where $\Lambda(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$ is the completed Riemann zeta function.
--
--   This is the cleanest possible form of the functional equation's consequence for zeros: it is an
--   immediate consequence of the symmetry $\Lambda(s) = \Lambda(1-s)$, and — unlike the
--   corresponding statement for $\zeta$ itself — it needs **no hypothesis on $\rho$**. The reason
--   is that $\Lambda$ absorbs the archimedean factor, so there are no trivial zeros and no
--   $\Gamma$-poles to exclude; the only exceptional points are $s = 0$ and $s = 1$, where $\Lambda$
--   has simple poles, and these are exchanged by the involution, so the orders still match.
--
--   Transferring the statement to $\zeta$ requires dividing by $\pi^{-s/2}\Gamma(s/2)$ and checking
--   it is a unit, which is where the strip hypothesis $0 < \Re\rho < 1$ enters. Recording the
--   $\Lambda$-version separately isolates the functional equation from that bookkeeping.
--
--   **Formalization note.** `analyticOrderAt` is valued in $\mathbb{N}\cup\{\infty\}$;
--   `completedRiemannZeta` is Mathlib's $\Lambda$.
-- source:
--   Classical; see Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1. Lean proof extracted from `Salt/SW/BoxFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace RiemannZetaOrders

theorem completed_order_one_sub (ρ : ℂ) :
    analyticOrderAt completedRiemannZeta (1 - ρ) = analyticOrderAt completedRiemannZeta ρ := by sorry

end RiemannZetaOrders
