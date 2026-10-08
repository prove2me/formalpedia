-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_unique_root_in_unit_disk
-- name    : QueueingFundamentals.Transient.unique_root_in_unit_disk
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:32:37.764622+00:00
-- url     : https://prove2.me/theorems/2020ee02-72e7-486c-ba9d-ee11fa27ab81
-- title:
--   Rouché step, §2.11.2 — $z_1$ is the only zero of the denominator of (2.73) in the unit disk
-- statement:
--   Let $\lambda, \mu > 0$ and let $s$ be a complex number with $\operatorname{Re} s > 0$. Let $r$ be the square root of $(\lambda+\mu+s)^2 - 4\lambda\mu$ whose real part is positive, and define, as in (2.74),
--
--   $$
--   z_1 = \frac{\lambda+\mu+s - r}{2\lambda}, \qquad z_2 = \frac{\lambda+\mu+s + r}{2\lambda}.
--   $$
--
--   Then $|z_1| < |z_2|$, and $z_1$ is the unique zero of the quadratic
--
--   $$ (\lambda+\mu+s)z - \mu - \lambda z^2 $$
--
--   in the open unit disk $|z| < 1$.
--
--   This is the root-location step that determines the unknown transform $\bar p_0(s)$ in (2.73): the numerator of (2.73) must vanish at $z_1$.
--
--   **Formalization Note** The square root is given as a hypothesis ($r^2 = (\lambda+\mu+s)^2 - 4\lambda\mu$, $\operatorname{Re} r > 0$) rather than through a branch of the complex square root. "In the unit circle" is read as the open disk.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.100, Eq. (2.74) and the application of Rouché's theorem, §2.11.2

import Mathlib

namespace QueueingFundamentals.Transient

/-- The Rouché step of §2.11.2 (p.100). Let `λ, μ > 0` and `Re s > 0`, and let `r` be the square
root of `(λ+μ+s)² - 4λμ` with positive real part. With
`z₁ = (λ+μ+s - r)/(2λ)` and `z₂ = (λ+μ+s + r)/(2λ)` as in (2.74), `|z₁| < |z₂|`, and `z₁` is
the only zero of `(λ+μ+s) z - μ - λ z²` in the open unit disk `|z| < 1`. -/
theorem unique_root_in_unit_disk (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    ‖((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))‖
        < ‖((lam : ℂ) + (mu : ℂ) + s + r) / (2 * (lam : ℂ))‖ ∧
      {z : ℂ | ‖z‖ < 1 ∧ ((lam : ℂ) + (mu : ℂ) + s) * z - (mu : ℂ) - (lam : ℂ) * z ^ 2 = 0}
        = {((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))} := by sorry

end QueueingFundamentals.Transient
