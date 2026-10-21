-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_diffusion_rankOneRegularity
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.diffusion_rankOneRegularity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:49:43.12546+00:00
-- url     : https://prove2.me/theorems/551de350-75f0-4547-a3f9-24c54099dd82
-- title:
--   Nonzero rank-one diffusion-domain elements have Dirichlet H2 factors
-- statement:
--   Let $G_0$ be the full trace-norm generator of the actual minimal absorbing diffusion on $H=L^2(\mathbb R_+)$, defined by the Dirichlet backward equation with $K=-d^2/dx^2$ and $L=\sqrt2\,d/dx$. Let $\psi,\varphi\in H$ be nonzero. If $\rho=|\psi\rangle\langle\varphi|$ belongs to $\operatorname{dom}G_0$, then $\psi,\varphi\in H^2\cap H^1_0$, and
--
--   $$
--   G_0\rho=2|\psi'\rangle\langle\varphi'|
--   +|\psi''\rangle\langle\varphi|
--   +|\psi\rangle\langle\varphi''|.
--   $$
--
--   Thus their differentiable representatives satisfy $\psi(0)=\varphi(0)=0$, and the corresponding kernel formula is $2\psi'(x)\overline{\varphi'(y)}+\psi''(x)\overline{\varphi(y)}+\psi(x)\overline{\varphi''(y)}$ almost everywhere. Their first derivatives have locally absolutely continuous representatives and no zero first-derivative boundary condition is imposed.
--
--   This extracts full Hilbert-space regularity from full generator-domain membership. **Source correction:** the printed subset sign means membership, and both factors must be nonzero: otherwise a rough factor paired with zero produces the zero domain element.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 8, Lemma 5: nonzero rank-one diffusion-domain elements have Dirichlet H2 factors

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

/-- PDF p.8, Lemma 5, corrected nonzero-factor reading: the printed unrestricted
implication fails if either factor is zero; the printed subset symbol means membership.
The conclusion uses the FULL actual diffusion-generator domain, not merely D0. -/
theorem diffusion_rankOneRegularity (b : HilbertBasis ℕ ℂ HalfLine)
    (Szero : TraceEvolution b) (Tzero : Evolution)
    (hDiffusion : IsAbsorbingDiffusion Tzero) (hPair : IsPredual b Szero Tzero)
    (f g : HalfLine) (hf : f ≠ 0) (hg : g ≠ 0)
    (rho : (TraceClass HalfLine)) (hRankOne : rho.val = InnerProductSpace.rankOne ℂ f g)
    (hDomain : rho ∈ TraceGeneratorDomain Szero) :
    ∃ (df ddf dg ddg : HalfLine) (eta : (TraceClass HalfLine)),
      DirichletTriple f df ddf ∧ DirichletTriple g dg ddg ∧
      InTraceGeneratorGraph Szero rho eta ∧
      eta.val = 2 • InnerProductSpace.rankOne ℂ df dg +
        InnerProductSpace.rankOne ℂ ddf g + InnerProductSpace.rankOne ℂ f ddg := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
