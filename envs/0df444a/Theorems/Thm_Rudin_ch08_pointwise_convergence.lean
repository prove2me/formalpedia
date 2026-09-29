-- Prove2me | Theorems.Thm_Rudin_ch08_pointwise_convergence
-- name    : Rudin.ch08_pointwise_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:28:20.1211+00:00
-- url     : https://prove2.me/theorems/598565cd-fdcc-4d7d-8f37-34ab73aae8ba
-- title:
--   Theorem 8.14 — pointwise convergence under a Lipschitz condition
-- statement:
--   If for some $x$ there are constants $\delta > 0$ and $M < \infty$ with $|f(x+t) - f(x)| \le M|t|$ for all $|t| < \delta$, then $s_N(f;x) \to f(x)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 189, Theorem 8.14

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.14: if there are constants `δ > 0` and `M < ∞` with
`|f (x + t) - f x| ≤ M |t|` for all `|t| < δ`, then the Fourier series of `f` converges to
`f x` at the point `x`. -/
theorem ch08_pointwise_convergence (f : ℝ → ℂ) (hper : HasPeriodTwoPi f)
    (hint : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (x : ℝ) (δ M : ℝ) (hδ : 0 < δ)
    (hlip : ∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) :
    Tendsto (fun N => fourierPartialSum f N x) atTop (𝓝 (f x)) := by sorry

end Rudin
