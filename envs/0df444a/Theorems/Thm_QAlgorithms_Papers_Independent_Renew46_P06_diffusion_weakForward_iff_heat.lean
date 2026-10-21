-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_diffusion_weakForward_iff_heat
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.diffusion_weakForward_iff_heat
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:52:50.098574+00:00
-- url     : https://prove2.me/theorems/079bbabc-a67e-4d7d-943e-4972361a1056
-- title:
--   Weak forward diffusion is equivalent to fiberwise absorbing heat evolution
-- statement:
--   Let $H=L^2(\mathbb R_+)$, let $\rho_0$ be an arbitrary complex trace-class operator, and let $t\mapsto\rho_t$ be a trace-class trajectory for $t\ge0$. Use trace-norm continuity and the initial condition $\rho_{t=0}=\rho_0$ in both Cauchy problems. The weak forward equation
--
--   $$
--   \frac{d}{dt}\langle f,\rho_t g\rangle
--   =2\langle f',\rho_t g'\rangle
--   +\langle f'',\rho_t g\rangle+\langle f,\rho_t g''\rangle,
--   \qquad f,g\in H^2\cap H^1_0,
--   $$
--
--   with a right derivative at zero, is equivalent to existence of a jointly measurable kernel representative which, for almost every $v=x-y$, solves
--
--   $$
--   \partial_t w(t,u,v)=4\partial_u^2 w(t,u,v),\qquad
--   u>|v|,\qquad w(t,|v|,v)=0\quad(t>0).
--   $$
--
--   The solution is classical in the positive-time/interior variables $(t,u)$ on almost every fiber and has the same trace-norm initial datum. No transverse smoothness in $v$ is asserted. Kernels represent the trajectory almost everywhere, with integrable operator actions. Equivalently, in $r=(u-|v|)/2$, the equation is $\partial_t w=\partial_r^2w$ on $r>0$, with continuous zero boundary trace at $r=0$.
--
--   This equivalence connects the operator weak Cauchy problem with characteristic heat evolution while preserving both directions and representative qualifications.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 12, Proposition 8: equivalence of weak forward diffusion and absorbing heat evolution

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P06

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State NuclearRepresentation traceNormValue operatorTrace)

open QAlgorithms.Papers.Independent.Claimed50.P50
  (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators
    IsUnitalQDS IsRelaxingEvolution)

open QAlgorithms.Papers.Independent.Next46.P09
  (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain
    DomainPerturbation IsMinimalPerturbation)

/-- PDF pp.12–13, Proposition 8: both implications for arbitrary trace-norm continuous
trace-class paths, with a fixed initial operator. Heat regularity is fiberwise for almost
all v, and equality of kernel versions is almost everywhere, never pointwise everywhere. -/
theorem diffusion_weakForward_iff_heat (rho : NNReal → (TraceClass HalfLine))
    (rhoInitial : (TraceClass HalfLine)) :
    WeakForwardCauchy rho rhoInitial ↔ HeatCauchy rho rhoInitial := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
