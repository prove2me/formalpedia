-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_arrival_pgf_eq_lst
-- name    : QueueingFundamentals.MG1.arrival_pgf_eq_lst
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:39:02.685498+00:00
-- url     : https://prove2.me/theorems/eeaf49a0-2646-4203-8836-10eb2e41469d
-- title:
--   Eq. (5.32) — K(z) = B*[λ(1 − z)]
-- statement:
--   Let $\lambda > 0$ and let $B$ be a service-time distribution on $[0,\infty)$ with Laplace–Stieltjes transform $B^*$. The generating function of the number of arrivals during a service time is, for every complex $z$ with $|z| \le 1$,
--
--   $$
--   K(z) = \int_0^\infty e^{-\lambda t(1-z)}\,dB(t) = B^*[\lambda(1-z)] .
--   $$
--
--   It turns statements about $K$ into statements about the service-time transform, which is how (5.33)–(5.34) are obtained from (5.16).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.237, Eq. (5.32)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.32), p.237: the generating function of the number of arrivals during a service time is
the Laplace–Stieltjes transform of the service distribution at `λ(1 - z)`:
`K(z) = ∫_0^∞ e^{-λt(1-z)} dB(t) = B*[λ(1 - z)]` for `|z| ≤ 1`. -/
theorem arrival_pgf_eq_lst (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    pgf (arrivalProb lam B) z = lst B ((lam : ℂ) * (1 - z)) := by sorry

end QueueingFundamentals.MG1
