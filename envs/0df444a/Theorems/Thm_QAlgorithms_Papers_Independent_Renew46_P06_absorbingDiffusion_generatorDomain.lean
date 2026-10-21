-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_absorbingDiffusion_generatorDomain
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.absorbingDiffusion_generatorDomain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:53:47.194342+00:00
-- url     : https://prove2.me/theorems/caff889c-d7c9-4c79-8daf-09671128b54d
-- title:
--   Full absorbing-diffusion generator domain with the corrected boundary condition
-- statement:
--   Let $G_0$ be the actual trace-norm generator of the minimal absorbing Dirichlet diffusion on $L^2(\mathbb R_+)$. For trace-class $\rho,\sigma$, define $p_v(r)=(r+\max(v,0),r+\max(-v,0))$. Then
--
--   $$
--   G_0\rho=\sigma\quad\Longleftrightarrow\quad
--   \begin{gathered}
--   \rho,\sigma\text{ admit integral kernels }k,q\text{ such that, for almost every }v,\\
--   F_v(r):=k(p_v(r))\text{ is locally absolutely continuous},\quad F_v(0)=0,\\
--   F_v'\text{ is locally absolutely continuous and }
--   F_v''(r)=q(p_v(r))\text{ for almost every }r>0.
--   \end{gathered}
--   $$
--
--   The first derivative is realized by its continuous representative, with its finite one-sided boundary value; no vanishing condition is imposed on that derivative. The left side includes full domain membership, and equality of kernels is almost everywhere. All kernel actions are integrable.
--
--   This gives both inclusions and the actual generator action. **Source correction:** the printed condition that $\rho(x+\xi,y+\xi)$ vanishes at $\xi=0$ is replaced by the proof's zero trace on the quadrant boundary. For an interior $(x,y)$ that boundary is reached at $\xi=-\min(x,y)$, not at zero.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 13, Proposition 9: full absorbing-diffusion generator domain

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

/-- PDF pp.13–14, Proposition 9, corrected boundary reading: printed "vanishes for
xi=0" is replaced by zero on the characteristic boundary r=0, as its proof explicitly
requires. Both directions and the generator action are stated on the full actual domain. -/
theorem absorbingDiffusion_generatorDomain (b : HilbertBasis ℕ ℂ HalfLine)
    (Szero : TraceEvolution b) (Tzero : Evolution)
    (hDiffusion : IsAbsorbingDiffusion Tzero) (hPair : IsPredual b Szero Tzero)
    (rho sigma : (TraceClass HalfLine)) :
    InTraceGeneratorGraph Szero rho sigma ↔ CharacteristicSecond rho sigma := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
