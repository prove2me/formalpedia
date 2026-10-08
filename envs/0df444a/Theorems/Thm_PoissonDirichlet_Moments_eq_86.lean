-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_eq_86
-- name    : PoissonDirichlet.Moments.eq_86
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:30.901982+00:00
-- url     : https://prove2.me/theorems/41990d1a-10db-4bdc-a644-80107978c959
-- title:
--   (86), p. 874 — negative moments of a positive random variable from its Laplace transform
-- statement:
--   Let $X$ be a random variable on a probability space with $X>0$ almost surely, and let $p>0$. Then
--
--   $$E\big[X^{-p}\big]=\frac{1}{\Gamma(p)}\int_0^\infty t^{p-1}\,E\big[e^{-tX}\big]\,dt,$$
--
--   as an identity in $[0,\infty]$: both sides may be $+\infty$.
--
--   The formula expresses negative moments through the Laplace transform. In the paper it turns Wendel's formula for the Laplace transform of $1/V_n$ into moments of $V_n$, and is the first step of the proof of Lemma 27.
--
--   **Formalization Note** Both sides are lower Lebesgue integrals of nonnegative functions, so the identity is meaningful when $E[X^{-p}]=\infty$. $X$ is assumed almost everywhere measurable (it is a random variable). The inner expectation $E[e^{-tX}]$ is the integral of a function bounded by $1$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 874, proof of Lemma 27, (86)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- (86), p. 874: negative moments of an a.s. positive random variable `X` through its
Laplace transform, `E[X^{-p}] = (1/Γ(p)) ∫_0^∞ t^{p-1} E[e^{-tX}] dt` for `p > 0`, stated in
`[0, ∞]` (both sides may be `+∞`). -/
theorem eq_86 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXm : AEMeasurable X P) (hX : ∀ᵐ ω ∂P, 0 < X ω) (p : ℝ) (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂P =
      ENNReal.ofReal (1 / Real.Gamma p) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1) * ∫ ω, Real.exp (-t * X ω) ∂P) := by sorry

end PoissonDirichlet.Moments
