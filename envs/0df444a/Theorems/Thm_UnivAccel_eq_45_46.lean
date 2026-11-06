-- Prove2me | Theorems.Thm_UnivAccel_eq_45_46
-- name    : UnivAccel.eq_45_46
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:01.695205+00:00
-- url     : https://prove2.me/theorems/1754ddea-e5c1-402e-9c29-36590c9c0ffd
-- title:
--   Eqs. (45)–(46) — with $h$ from (43), $N=\lceil 8\log 2/(3h\sqrt\mu)\rceil = O(1+(\mathcal H/(\mu r^2))^{1/3})$ steps halve the potential
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$, $f(0) = \min f = 0$, $r > 0$, and let $\mathcal H > 0$ be an upper bound on the initial potential $H^{la}_0$. Fix the duration (43),
--   $$
--   h = \frac{1}{\sqrt\mu}\min\Big\{\frac12, \Big(\frac{\mu r^2}{\mathcal H}\Big)^{1/3}\Big\},
--   $$
--   and run the lookahead method (44): $x_{c,i} = \mathrm{Ball}^f_r(x_{p,i})$ and $(\bar x_{i+1}, \bar w_{i+1})$ the update (44) of $(\bar x_i, \bar w_i)$. With $H^{la}_i = f(\bar x_i) + \frac12\|\bar w_i\|^2$:
--   1. every step satisfies $H^{la}_+ \le (1 - \frac38 h\sqrt\mu)\, H^{la}$;
--   2. for every $N$,
--   $$
--   H^{la}_N \le \Big(1 - \frac38 h\sqrt\mu\Big)^N H^{la}_0 \le e^{-3Nh\sqrt\mu/8} H^{la}_0; \tag{45}
--   $$
--   3. $N = \lceil 8\log 2/(3h\sqrt\mu)\rceil \le C\big(1 + (\mathcal H/(\mu r^2))^{1/3}\big)$, and these $N$ iterations halve the potential, $H^{la}_N \le H^{la}_0/2$ (46).
--
--   This is the per-block cost of the lookahead method in ball queries; with $\mathcal H$ of order $\mu R^2$ it is the Monteiro–Svaiter rate $O(1 + (R/r)^{2/3})$.
--
--   Differences from the source:
--   - generalization: (45) "unless a ball query returns the minimizer earlier" → (45) for every N, with the sequence continued by (44) also after a query returns the minimizer; reason: when ∇f(x_c) = 0, η = 1/μ ≥ 4h² so α = 1 and Lemma 2 still gives the contraction; the page's claim is the case with no such query
--   - reading: N = O(1 + (𝓗/(μr²))^{1/3}) → ∃ C > 0 quantified before n, f, μ, r, 𝓗 and the iterates; reason: O(·) as an absolute constant
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.3, eqs. (43), (45), (46), pp.23–24

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_laUpdate

namespace UnivAccel

/-- (45)–(46), §5.3, pp.23–24 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)). Let `f` be differentiable and `μ`-strongly convex,
`μ > 0`, `f(0) = min f = 0`, `r > 0`, and let `𝓗 > 0` be an upper bound on `H^la_0`. Fix `h` by
(43), `h = (1/√μ) min{1/2, (μr²/𝓗)^{1/3}}`, and run (44): `x_c,i = Ball^f_r(x_p,i)` and
`(x̄_{i+1}, w̄_{i+1})` the update (44) of `(x̄_i, w̄_i)`. With `H^la_i = f(x̄_i) + ½‖w̄_i‖²`: every step
satisfies `H^la₊ ≤ (1 − (3/8)h√μ) H^la`; for every `N`,
`H^la_N ≤ (1 − (3/8)h√μ)^N H^la_0 ≤ e^{−3Nh√μ/8} H^la_0` (45); and
`N = ⌈8 log 2/(3h√μ)⌉ = O(1 + (𝓗/(μr²))^{1/3})` iterations halve the potential (46).

**Formalization Note** `O(·)` is an absolute constant `C > 0` quantified before everything else.
The sequence continues by (44) even if a query returns the minimizer, where the method itself
would stop. -/
theorem eq_45_46 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r Hbar : ℝ)
      (xs ws xcs : ℕ → EuclideanSpace ℝ (Fin n)),
      Differentiable ℝ f → StrongConvexOn Set.univ μ f → 0 < μ →
      f 0 = 0 → (∀ y, f 0 ≤ f y) → 0 < r → 0 < Hbar →
      (∀ i, IsBallMin f (laPredict μ (laStepSize μ r Hbar) (xs i) (ws i)) r (xcs i)) →
      (∀ i, (xs (i + 1), ws (i + 1))
        = laUpdate μ r (laStepSize μ r Hbar) (xs i) (ws i) (xcs i) (gradient f (xcs i))) →
      f (xs 0) + 1 / 2 * ‖ws 0‖ ^ 2 ≤ Hbar →
      let h := laStepSize μ r Hbar
      let H : ℕ → ℝ := fun i => f (xs i) + 1 / 2 * ‖ws i‖ ^ 2
      (∀ i, H (i + 1) ≤ (1 - 3 / 8 * h * Real.sqrt μ) * H i) ∧
      (∀ N : ℕ, H N ≤ (1 - 3 / 8 * h * Real.sqrt μ) ^ N * H 0 ∧
        (1 - 3 / 8 * h * Real.sqrt μ) ^ N * H 0
          ≤ Real.exp (-(3 * N * h * Real.sqrt μ / 8)) * H 0) ∧
      ((⌈8 * Real.log 2 / (3 * h * Real.sqrt μ)⌉₊ : ℕ) : ℝ)
          ≤ C * (1 + (Hbar / (μ * r ^ 2)) ^ ((1 : ℝ) / 3)) ∧
      H ⌈8 * Real.log 2 / (3 * h * Real.sqrt μ)⌉₊ ≤ H 0 / 2 := by sorry

end UnivAccel
