-- Prove2me | Theorems.Thm_Rudin_ch08_trig_approximation
-- name    : Rudin.ch08_trig_approximation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:29:28.497168+00:00
-- url     : https://prove2.me/theorems/c37f7890-5a5b-4d70-be41-fd3db5873ad9
-- title:
--   Theorem 8.15 — uniform approximation by trigonometric polynomials
-- statement:
--   If $f$ is continuous with period $2\pi$ and $\varepsilon > 0$, there is a trigonometric polynomial $P$ with $|P(x) - f(x)| < \varepsilon$ for all real $x$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 190, Theorem 8.15

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.15: a continuous `2π`-periodic function can be uniformly approximated by
trigonometric polynomials. -/
theorem ch08_trig_approximation (f : ℝ → ℂ) (hcont : Continuous f) (hper : HasPeriodTwoPi f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℝ → ℂ, IsTrigPolynomial P ∧ ∀ x : ℝ, ‖P x - f x‖ < ε := by sorry

end Rudin
