-- Prove2me | Theorems.Thm_PsdPermanent_log_normSq_gaussian
-- name    : PsdPermanent.log_normSq_gaussian
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:38.026689+00:00
-- url     : https://prove2.me/theorems/e991f074-b1f0-46ef-8b44-23ebdac7e70b
-- title:
--   §3, p.3 and Eq. (2) — $|g|^2\sim\mathrm{Exp}(1)$, $\mathbb E\log|g|^2=-\gamma$
-- statement:
--   Let $g\sim\mathcal{CN}(0,1)$. Then $|g|^2\sim\mathrm{Exp}(1)$, the functions $t\mapsto e^{-t}\log t$ on $(0,\infty)$ and $w\mapsto\log|w|^2$ against the law of $g$ are integrable, and
--   $$\mathbb E[\log|g|^2]=\int_0^\infty e^{-t}\log t\,dt=\Gamma'(1)=-\gamma,$$
--   where $\gamma$ is the Euler–Mascheroni constant.
--
--   This one-dimensional constant is the whole loss per factor in the sandwich.
--
--   Differences from the source: none.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3; Eq. (2), p.4

import Mathlib
import Definitions.Def_PsdPermanent_cnScalarDensity
open MeasureTheory
open ProbabilityTheory

namespace PsdPermanent

/-- **|g|² is exponential, and Eq. (2).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3 and Eq. (2), p.4: "If g ∼ CN(0, 1), then |g|² ∼ Exp(1), because the squared radius of a two-dimensional
real Gaussian with covariance I_2/2 is exponential. Consequently, E[log|g|²] = ∫_0^∞ e^{−t} log t dt = Γ′(1) = −γ."

**Formalization Note.** The law of `g` is `cnScalarDensity 1` on `ℂ`; `Exp(1)` is Mathlib's
`ProbabilityTheory.expMeasure 1`; `γ` is `Real.eulerMascheroniConstant`. Integrability is part of the conclusion. -/
theorem log_normSq_gaussian :
    (volume.withDensity fun w : ℂ => ENNReal.ofReal (cnScalarDensity 1 w)).map Complex.normSq = expMeasure 1 ∧
      IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Set.Ioi 0) ∧
      (∫ w : ℂ, Real.log (Complex.normSq w) * cnScalarDensity 1 w) =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * Real.log t ∧
      Integrable (fun w : ℂ => Real.log (Complex.normSq w) * cnScalarDensity 1 w) ∧
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * Real.log t) = deriv Real.Gamma 1 ∧
      deriv Real.Gamma 1 = -Real.eulerMascheroniConstant := by sorry

end PsdPermanent
