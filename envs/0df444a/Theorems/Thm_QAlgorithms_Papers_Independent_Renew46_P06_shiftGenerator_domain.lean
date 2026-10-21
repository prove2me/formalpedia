-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_shiftGenerator_domain
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.shiftGenerator_domain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:44:04.364231+00:00
-- url     : https://prove2.me/theorems/c1baa61f-ce52-4746-93e9-adaf4d17fb53
-- title:
--   Full domain and action of the left-shift trace-class generator
-- statement:
--   Let $W_t f(x)=f(x+t)$ on $H=L^2(\mathbb R_+)$, let $S_t^0\rho=W_t\rho W_t^*$, and let $G_0$ be its actual trace-norm generator. For real $v$ and $r\ge0$, write $p_v(r)=(r+\max(v,0),r+\max(-v,0))$. For any trace-class operators $\rho,\sigma$, the following are equivalent:
--
--   $$
--   G_0\rho=\sigma\quad\Longleftrightarrow\quad
--   \begin{gathered}
--   \rho,\sigma\text{ have kernels }k,q\text{ such that, for almost every }v,\\
--   F_v(r):=k(p_v(r))\text{ is locally absolutely continuous on }[0,\infty),\\
--   F_v'(r)=q(p_v(r))\text{ for almost every }r>0.
--   \end{gathered}
--   $$
--
--   The left side includes membership of $\rho$ in the full generator domain. Kernels are actual $L^2$ integral kernels, and every integral defining their operator action is integrable. There is no zero boundary condition in the shift model.
--
--   The equivalence identifies both the entire domain and the generator value, rather than a restriction to finite-rank tests.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 3, Proposition 1: full shift-generator domain

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

/-- PDF pp.3,6–7, Proposition 1: both directions of the full domain/action description.
The actual shift is specified by translation on every L2 vector, without a boundary condition. -/
theorem shiftGenerator_domain (b : HilbertBasis ℕ ℂ HalfLine)
    (W : ContractionSemigroup HalfLine) (hShift : IsLeftShift W)
    (Szero : TraceEvolution b) (Tzero : Evolution)
    (hPair : IsShiftPair b W Szero Tzero) (rho sigma : (TraceClass HalfLine)) :
    InTraceGeneratorGraph Szero rho sigma ↔ CharacteristicFirst rho sigma := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
