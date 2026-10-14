-- Prove2me | Theorems.Thm_TelehealthParity_Access_corollary_1
-- name    : TelehealthParity.Access.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:06.910986+00:00
-- url     : https://prove2.me/theorems/fd5c6347-250a-4280-b74b-e3b1032f255f
-- title:
--   Corollary 1 — $F(r,\theta)$ is maximized at $\theta=0$ or at $\theta=\theta^*$
-- statement:
--   Under the standing assumptions, let $q$ be admissible and let $r>0$, and assume that $r\le R$ or $\theta^O\le\theta^*$. Then over $\theta\in[0,1]$ the provider's revenue $F(r,\theta)$ attains its maximum at $\theta=0$ or at $\theta=\theta^*$:
--   $$F(r,\theta)\le F(r,0)\ \ \forall\theta\in[0,1]\qquad\text{or}\qquad F(r,\theta)\le F(r,\theta^*)\ \ \forall\theta\in[0,1].$$
--
--   The provider therefore either runs an office-only practice or chooses the telehealth commitment that maximizes telehealth usage.
--
--   **Formalization Note** The hypothesis "$r\le R$ or $\theta^O\le\theta^*$" is not in the printed corollary, which claims the conclusion for every $r>0$. As printed it is false: the paper's $\theta^*$ is the first-order point (24), which can lie below $\theta^O$, and when moreover $r>R$ the revenue increases on $[\theta^T,\theta^O)$ and is maximized at $\theta^O$ (e.g. $V=9.64$, $c_T=1.84$, $c_O=3.02$, $\tau=2.41$, $h=0.267$, $\mu=1.73$, $q=0.706$, $r=3.6R$). Pay parity $r=R$ is covered. $\theta^*$ always lies in $(0,1)$ for admissible $q$.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 17, Corollary 1, with θ* of eq. (24)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

theorem corollary_1 (p : Params) (hp : p.Standing) (q : ℝ) (hq : Admissible p q)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ p.R ∨ thetaO p q ≤ thetaStar p q) :
    IsMaxOn (revenue p q r) (Set.Icc 0 1) 0 ∨
      IsMaxOn (revenue p q r) (Set.Icc 0 1) (thetaStar p q) := by sorry

end TelehealthParity.Access
