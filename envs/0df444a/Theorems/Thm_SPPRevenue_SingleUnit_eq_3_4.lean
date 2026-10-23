-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_eq_3_4
-- name    : SPPRevenue.SingleUnit.eq_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:03.653445+00:00
-- url     : https://prove2.me/theorems/30cb1586-e94d-4dd2-91e4-38f8597171af
-- title:
--   Inequalities (3)–(4), p. 14 — MP = ∫_0^∞ m(τ) dτ and m(τ) ≥ 1 − exp(−s⋆(τ))
-- statement:
--   Let $t$ be a single-unit threshold mechanism for $n$ buyers with independent values, MP the expected revenue of the Myersonian sequential posted-price mechanism, and $m(\tau)$ the probability that some buyer has $v_i \ge t'_i \ge \tau$. Then
--   $$\mathrm{MP} = \int_0^\infty m(\tau)\,d\tau \qquad\text{and}\qquad m(\tau) \ge 1 - \exp\big(-s^\star(\tau)\big) = f\big(s^\star(\tau)\big) \ \text{ for every } \tau.$$
--
--   Together with the normalization $\mathrm{MP} \le 1$ these give the second constraint $\int_0^\infty f(s^\star(\tau))\,d\tau \le 1$ of the factor-revealing program.
--
--   **Formalization Note** The printed "$\le 1$" in (3) is the proof's normalization $\max(\mathrm{MP},\mathrm{UP}) = 1$ and is not stated. The identity uses that the single-unit sequential sale sells at a price of at least $\tau$ exactly when some buyer has $v_i \ge t'_i \ge \tau$; that is part of what is to be proved, not an assumption. The integral is over $(0,\infty)$ in $[0,\infty]$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 14, §4.1, Inequalities (3)–(4)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

theorem eq_3_4 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) :
    mpRev μ t = ∫⁻ τ in Set.Ioi 0, mSell μ t τ ∧
      ∀ τ : ℝ, ENNReal.ofReal (1 - Real.exp (-(sStar μ t τ).toReal)) ≤ mSell μ t τ := by sorry

end SPPRevenue.SingleUnit
