-- Prove2me | Theorems.Thm_UnivAccel_eq_41_42
-- name    : UnivAccel.eq_41_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:53.625894+00:00
-- url     : https://prove2.me/theorems/ad7762ed-fa32-40c7-80d7-9faba222e23a
-- title:
--   Eqs. (41)–(42) — undamped steps contract, damped steps lose $3r^2/(8h^2)$
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$ and $f(0) = \min f = 0$, and let $r > 0$ and $0 < h\sqrt\mu \le 1/2$. Take one step of the lookahead method (44) from $(\bar x, \bar w)$, with $x_c = \mathrm{Ball}^f_r(x_p)$, $\eta = r/(\|\nabla f(x_c)\| + \mu r)$ and $\alpha = \min\{1, \eta/h^2\}$ (40), and write $H^{la} = f(\bar x) + \frac12\|\bar w\|^2$. Then:
--   1. if $\alpha = 1$,
--   $$
--   H^{la} - H^{la}_+ \ge h\sqrt\mu\, H^{la}; \tag{41}
--   $$
--   2. if $\alpha < 1$, then $\alpha = \eta/h^2$, $\eta < h^2$, and
--   $$
--   H^{la} - H^{la}_+ \ge \frac{\alpha r}{2}\|\nabla f(x_c)\| = \frac{r^2}{2h^2}(1 - \mu\eta) \ge \frac{3r^2}{8h^2}. \tag{42}
--   $$
--
--   Undamped steps give geometric contraction and damped steps a decrease of order $h^{-2}$; the choice (43) of $h$ balances the two.
--
--   Differences from the source:
--   - encoding: one step of (27) with the ball oracle (36) and α from (40) → the update (44) (laUpdate) with gradient ∇f(x_c); reason: (44) is that step with λ(x_p − x_c) = ∇f(x_c) substituted (eq. (36)); the iterates are the same
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.3, eqs. (40)–(42), p.23

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_laUpdate

namespace UnivAccel

/-- (41)–(42), §5.3, p.23 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)). Under the hypotheses of Lemma 2 (`f` differentiable,
`μ`-strongly convex, `μ > 0`, `f(0) = min f = 0`, `r > 0`), suppose `h√μ ≤ 1/2` and take
`α = min{1, η/h²}` (40), with one step of (44): `x_c = Ball^f_r(x_p)` at
`x_p = (x̄ + h w̄)/(1 + h√μ)`, `η = r/(‖∇f(x_c)‖ + μr)`, `(x̄₊, w̄₊)` the update (44), and
`H^la = f(x̄) + ½‖w̄‖²`. If `α = 1`, then `H^la − H^la₊ ≥ h√μ H^la` (41). If `α < 1`, then
`α = η/h²`, `η < h²` and
`H^la − H^la₊ ≥ (αr/2)‖∇f(x_c)‖ = (r²/2h²)(1 − μη) ≥ 3r²/(8h²)` (42). -/
theorem eq_41_42 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r h : ℝ)
    (xbar wbar xc : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ μ f) (hμ : 0 < μ)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (hr : 0 < r)
    (hh : 0 < h * Real.sqrt μ) (hh1 : h * Real.sqrt μ ≤ 1 / 2)
    (hxc : IsBallMin f (laPredict μ h xbar wbar) r xc) :
    let g := gradient f xc
    let α := laAlpha μ r h g
    let η := laEta μ r g
    let p := laUpdate μ r h xbar wbar xc g
    let H := f xbar + 1 / 2 * ‖wbar‖ ^ 2
    let H' := f p.1 + 1 / 2 * ‖p.2‖ ^ 2
    (α = 1 → H - H' ≥ h * Real.sqrt μ * H) ∧
    (α < 1 → α = η / h ^ 2 ∧ η < h ^ 2 ∧
      H - H' ≥ α * r / 2 * ‖g‖ ∧
      α * r / 2 * ‖g‖ = r ^ 2 / (2 * h ^ 2) * (1 - μ * η) ∧
      r ^ 2 / (2 * h ^ 2) * (1 - μ * η) ≥ 3 * r ^ 2 / (8 * h ^ 2)) := by sorry

end UnivAccel
