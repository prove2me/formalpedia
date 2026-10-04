-- Prove2me | Theorems.Thm_StochApproxDyn_Interpolation_interpAffine_sub_eq_integral
-- name    : StochApproxDyn.Interpolation.interpAffine_sub_eq_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:08:03.626141+00:00
-- url     : https://prove2.me/theorems/31f63780-99e4-446a-bc1f-7394b96a2e92
-- title:
--   Section 4.1, Eq. (9) — the interpolated process solves the integral form of (7)
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$ be continuous, let the step sizes satisfy $\gamma_n\ge0$, $\sum_n\gamma_n=\infty$, $\gamma_n\to0$, and let $\{x_n\}$ follow the scheme $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$. Let $X$ be the affine interpolation of $\{x_n\}$ on the time scale $\tau_n=\sum_{i\le n}\gamma_i$, $\overline X$ the piecewise constant interpolation and $\overline U$ the piecewise constant interpolation of the perturbations. Then for every $t\ge0$
--   $$X(t)-X(0)=\int_0^t\big[F(\overline X(s))+\overline U(s)\big]\,ds .$$
--
--   Equation (9) turns the discrete recursion into an integral equation that differs from the integral form of $\dot x=F(x)$ only by the replacement of $X$ with $\overline X$ and by the noise integral; every later comparison with the flow of $F$ starts from it.
--
--   **Formalization Note** The integral is the interval integral of a piecewise constant function, which is integrable on $[0,t]$ under the standing assumptions, so no junk value enters.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 12, Section 4.1, Eq. (9)

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, §4.1, Eq. (9), p. 12: under the standing assumptions on `γ` and the recursion (7),
the affine interpolated process solves the integral form of (7):
`X(t) − X(0) = ∫_0^t [F(X̄(s)) + Ū(s)] ds` for every `t ≥ 0`. -/
theorem interpAffine_sub_eq_integral {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (t : ℝ) (ht : 0 ≤ t) :
    interpAffine γ x t - interpAffine γ x 0 =
      ∫ s in (0 : ℝ)..t, (F (interpConst γ x s) + noiseInterp γ U s) := by sorry

end StochApproxDyn.Interpolation
