-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P09_minimal_CP_perturbation
-- name    : QAlgorithms.Papers.Independent.Next46.P09.minimal_CP_perturbation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:04:31.339479+00:00
-- url     : https://prove2.me/theorems/9f36a32a-4bd9-4b50-b585-86270e1374b4
-- title:
--   Minimal completely positive perturbation of an arbitrary dynamical generator
-- statement:
--   Let $H$ be a separable complete complex Hilbert space and let $L^0$ be the actual trace-norm generator of a completely positive, trace-nonincreasing dynamical semigroup on $\mathcal T(H)$. Let $P:\operatorname{dom}L^0\to\mathcal T(H)$ be complex linear and completely positive at every finite matrix level. Assume
--
--   $$\operatorname{tr}P(\rho)\le-\operatorname{tr}L^0(\rho)\qquad(0\le\rho\in\operatorname{dom}L^0).$$
--
--   For every $\lambda>0$, let $R^0_\lambda$ be the actual Laplace resolvent of the original semigroup. Then $PR^0_\lambda$ is a complex linear completely positive map on the full trace class, and
--
--   $$R_\lambda\rho=\sum_{n=0}^\infty R^0_\lambda(PR^0_\lambda)^n\rho$$
--
--   converges in trace norm for every $\rho\in\mathcal T(H)$. The limits are the actual resolvents of a dynamical semigroup. Furthermore $R_\lambda$ solves
--
--   $$X=R^0_\lambda+XPR^0_\lambda$$
--
--   and is its smallest completely positive solution: every complex linear completely positive solution $X$ satisfies that $X-R_\lambda$ is completely positive. The initial generator need not be a no-event generator, and convergence of the series is strong rather than an asserted operator-norm convergence. This construction supplies the minimal semigroup used in later perturbations.
-- source:
--   Unbounded generators of dynamical semigroups, arXiv:1707.02266v1, PDF p. 8, Proposition II.4: minimal completely positive perturbation

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P09

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass IsTraceClass traceNormValue operatorTrace IsPositive)

open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Proposition II.4, arXiv:1707.02266v1, PDF pp.8–9.
Tzero is arbitrary, and need not be a no-event semigroup. The conclusion
includes strong convergence of (16), an actual dynamical semigroup, the
fixed-point equation, and minimality in completely positive order. -/
theorem minimal_CP_perturbation [TopologicalSpace.SeparableSpace H]
    {I : Type v} (b : HilbertBasis I ℂ H) (Tzero : TraceDynamicalSemigroup b)
    (P : DomainPerturbation Tzero) :
    ∃ T : TraceDynamicalSemigroup b, IsMinimalPerturbation Tzero P T := by sorry

end QAlgorithms.Papers.Independent.Next46.P09

end
