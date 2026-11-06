-- Prove2me | Theorems.Thm_UnivAccel_lemma_2
-- name    : UnivAccel.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:44.437726+00:00
-- url     : https://prove2.me/theorems/a2196397-cded-435e-a3bc-b57a447b0cf1
-- title:
--   Lemma 2 — potential decrease for a ball lookahead step, (37)
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$ and $f(0) = \min f = 0$. Let $r > 0$ and $0 < h\sqrt\mu \le 1$. Consider one step of the lookahead algorithm (27) with the ball oracle (36): from $(\bar x, \bar w)$,
--   $$
--   x_p = \frac{\bar x + h\bar w}{1 + h\sqrt\mu}, \quad x_c = \mathrm{Ball}^f_r(x_p), \quad \lambda = \frac{\|\nabla f(x_c)\|}{r}, \quad \eta = \frac{r}{\|\nabla f(x_c)\| + \mu r},
--   $$
--   $$
--   \bar x_+ = \bar x + \alpha(x_c - \bar x), \qquad \bar w_+ = \bar w - \alpha h\big(\lambda(x_p - x_c) + \sqrt\mu\,\bar w - \mu x_c\big),
--   $$
--   with $\alpha$ any number satisfying $0 < \alpha \le 1$ and $\eta \ge \alpha h^2$. With the potential $H^{la} = f(\bar x) + \frac12\|\bar w\|^2$,
--   $$
--   H^{la}_+ \le (1 - \alpha^2 h\sqrt\mu)\, H^{la} - \frac{\alpha r}{2}\|\nabla f(x_c)\|. \tag{37}
--   $$
--
--   This is the key one-step inequality behind the Monteiro–Svaiter rate of the lookahead method: it gives contraction for undamped steps and a decrease of order $r^2/h^2$ for damped ones.
--
--   Differences from the source: none.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), Lemma 2, eq. (37), pp.21–22

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_laUpdate

namespace UnivAccel

/-- Lemma 2 (Potential decrease for a ball lookahead step), (37), pp.21–22 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)). Let
`f : ℝⁿ → ℝ` be differentiable and `μ`-strongly convex, with `μ > 0` and `f(0) = min f = 0`. Let
`r > 0` and `0 < h√μ ≤ 1`. Consider one step of the algorithm (27) with the ball oracle (36):
`x_p = (x̄ + h w̄)/(1 + h√μ)`, `x_c = Ball^f_r(x_p)`, `λ = ‖∇f(x_c)‖/r`, `η = r/(‖∇f(x_c)‖ + μr)`,
`x̄₊ = x̄ + α(x_c − x̄)`, `w̄₊ = w̄ − αh(λ(x_p − x_c) + √μ w̄ − μ x_c)`, with `α` replaced by any number
satisfying `0 < α ≤ 1` and `η ≥ αh²`. Then, with `H^la = f(x̄) + ½‖w̄‖²`,
`H^la₊ ≤ (1 − α²h√μ) H^la − (αr/2)‖∇f(x_c)‖`. -/
theorem lemma_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r h α : ℝ)
    (xbar wbar xc : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ μ f) (hμ : 0 < μ)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (hr : 0 < r)
    (hh : 0 < h * Real.sqrt μ) (hh1 : h * Real.sqrt μ ≤ 1)
    (hxc : IsBallMin f (laPredict μ h xbar wbar) r xc)
    (hα : 0 < α) (hα1 : α ≤ 1) (hη : α * h ^ 2 ≤ laEta μ r (gradient f xc)) :
    f (xbar + α • (xc - xbar))
        + 1 / 2 * ‖wbar - (α * h) • ((‖gradient f xc‖ / r) • (laPredict μ h xbar wbar - xc)
            + Real.sqrt μ • wbar - μ • xc)‖ ^ 2
      ≤ (1 - α ^ 2 * h * Real.sqrt μ) * (f xbar + 1 / 2 * ‖wbar‖ ^ 2)
        - α * r / 2 * ‖gradient f xc‖ := by sorry

end UnivAccel
