-- Prove2me | Theorems.Thm_Sherlocking_InfoPolicy_oc0_iff_ineq4
-- name    : Sherlocking.InfoPolicy.oc0_iff_ineq4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:17.314357+00:00
-- url     : https://prove2.me/theorems/67c5b8ef-e318-4e20-9826-6d18e261679f
-- title:
--   Proposition 3 (second clause), p. 15 (PDF 17) — at any fee r < 1 − K, (OC0) is equivalent to inequality (4)
-- statement:
--   Let $\delta<1$ and $K$ satisfy Assumption 1, $1-\delta<K<\delta$, and let $0\le r<1-K$. Then the obedience constraint (OC0) under signal (3),
--   $$\mathbb E[\theta\mid x=0;\ \theta\ge\theta_S(r)]\le\theta_P(r),$$
--   holds if and only if
--   $$\int_{\theta_P(r)}^{1}(\theta-\theta_P(r))\,(1-\alpha(\theta;r))\,d\theta\ \le\ \int_{\theta_S(r)}^{\theta_P(r)}(\theta_P(r)-\theta)\,d\theta. \tag{4}$$
--
--   This is the "which is equivalent to" clause of Proposition 3, stated at a general fee rather than at $r^C$. The right side of (4) is the platform's "budget" for no-entry obedience, and the left side its "spending".
--
--   **Formalization Note** $\delta<1$ and $r<1-K$ are added; the latter makes the denominator of the conditional expectation in (OC0) positive.
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), p. 15 (PDF 17), Proposition 3, Eq. (4)

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Sherlocking.InfoPolicy

theorem oc0_iff_ineq4 (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r) (hrK : r < 1 - K) : OC0 K δ r ↔ Ineq4 K δ r := by sorry

end Sherlocking.InfoPolicy
