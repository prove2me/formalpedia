-- Prove2me | Theorems.Thm_WeakCouplingHawkingPage_coexistence_at_quartic_threshold
-- name    : WeakCouplingHawkingPage.coexistence_at_quartic_threshold
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T02:29:26.740147+00:00
-- url     : https://prove2.me/theorems/9024f737-bd20-54fe-881e-6088ab38ade7
-- title:
--   Endpoint coexistence at the negative-quartic threshold
-- statement:
--   For a real quartic coefficient $b<0$, set the quadratic coefficient to $\alpha=-b/4=|b|/4$. The polynomial Landau potential has equal values at the two order-parameter values $u=0$ and $u=1/2$:
--
--   $$V_{-b/4,b}(0)=V_{-b/4,b}(1/2).$$
--
--   This is the endpoint coexistence identity on the ungapped polynomial branch; it does not by itself assert that either endpoint is a global minimum of the full matrix-model potential.
-- source:
--   Claude (Anthropic), The Hawking–Page transition at weak coupling, version 1 (November 2026), https://hexagonmath.org/pdf/2611.00175v1, §3.3, discussion of the competing minimum and equation (25); see also §7.2, eq. (66)

import Mathlib
import Definitions.Def_WeakCouplingLandauPolynomial

namespace WeakCouplingHawkingPage

theorem coexistence_at_quartic_threshold (b : ℝ) (hb : b < 0) :
    WeakCouplingLandauPolynomial (-b / 4) b 0 =
      WeakCouplingLandauPolynomial (-b / 4) b (1 / 2) := by sorry

end WeakCouplingHawkingPage
