-- Prove2me | Theorems.Thm_RiemannZetaOrders_zeta_order_completed
-- name    : RiemannZetaOrders.zeta_order_completed
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:41:51.917266+00:00
-- url     : https://prove2.me/theorems/1ea47250-2735-4f27-ba75-98026846b56a
-- title:
--   The zeros of $\zeta$ and of the completed zeta agree in the right half-plane
-- statement:
--   **$\zeta$ and the completed zeta function have the same zeros, to the same order, in the
--   right half-plane.**
--
--   Let $\Lambda(s)$ denote the completed Riemann zeta function, related to $\zeta$ by
--
--   $$\Lambda(s) \;=\; \pi^{-s/2}\,\Gamma\!\left(\tfrac{s}{2}\right)\zeta(s).$$
--
--   Then for every $w$ with $\Re w > 0$, $w \ne 0$ and $w \ne 1$, the orders of vanishing agree:
--
--   $$\operatorname{ord}_{w}\zeta \;=\; \operatorname{ord}_{w}\Lambda .$$
--
--   The two functions differ by the archimedean factor $\pi^{-s/2}\Gamma(s/2)$, which on the region
--   $\Re s > 0$ is **holomorphic and non-vanishing**: $\Gamma$ has no zeros anywhere, and its poles
--   sit at $s = 0, -2, -4, \dots$, all excluded by $\Re w > 0$ together with $w \ne 0$. Multiplying
--   by a unit cannot change the order of vanishing, so the zero sets and multiplicities coincide.
--
--   The point $w = 1$ is excluded because $\zeta$ has its simple pole there while $\Lambda$ does
--   too, so neither has a well-defined order of *vanishing* at that point.
--
--   This is the elementary but indispensable bookkeeping step that lets one work with $\Lambda$ —
--   which satisfies the clean symmetric functional equation $\Lambda(s) = \Lambda(1-s)$ and is
--   entire apart from its two poles — and then transfer conclusions about zeros back to $\zeta$.
--   Every argument that reflects a zero $\rho$ to $1-\rho$, or that counts zeros via a Hadamard
--   product for $\Lambda$, relies on it.
--
--   **Formalization note.** `analyticOrderAt` is Mathlib's order of vanishing, valued in
--   $\mathbb{N}\cup\{\infty\}$, and `completedRiemannZeta` is $\Lambda$.
-- source:
--   Classical; see Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1, and Iwaniec & Kowalski, *Analytic Number Theory*, §5.1. Lean proof extracted from `Salt/SW/BoxFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace RiemannZetaOrders

theorem zeta_order_completed {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwre : 0 < w.re) :
    analyticOrderAt riemannZeta w = analyticOrderAt completedRiemannZeta w := by sorry

end RiemannZetaOrders
