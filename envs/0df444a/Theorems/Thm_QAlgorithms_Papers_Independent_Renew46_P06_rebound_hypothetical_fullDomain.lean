-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_rebound_hypothetical_fullDomain
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.rebound_hypothetical_fullDomain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:51:09.251362+00:00
-- url     : https://prove2.me/theorems/b7d9df89-cbcd-42a4-91af-67682789d556
-- title:
--   A hypothetical standard rebound representation has exactly the Dirichlet domain
-- statement:
--   Let $\Omega$ be any density on $H=L^2(\mathbb R_+)$. Consider the actual minimal reset of the absorbing diffusion defined by the Dirichlet backward equation. Assume that its dual has a standard realization with a maximal accretive Hilbert operator $K$, taken on its full closed domain, and a countable jump family satisfying the source's dissipativity condition. Then
--
--   $$
--   \operatorname{dom}K=H^2(\mathbb R_+)\cap H^1_0(\mathbb R_+)=AC_0^2(\mathbb R_+).
--   $$
--
--   On the right, each vector has a differentiable representative vanishing at zero, with locally absolutely continuous first derivative and square-integrable second derivative. Its first derivative is not required to vanish at zero.
--
--   The conclusion is equality of the entire Hilbert-generator domain. The preceding inclusion, the rank-one generator identity and gauge formulas are not hypotheses.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 9, Lemma 7: hypothetical standard representation has the full Dirichlet domain

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

/-- PDF pp.9–10, Lemma 7: under the hypothetical full-domain standard realization,
the entire Hilbert-generator domain is the Dirichlet H2 domain. No derived inclusion,
gauge formula, or differential expression is assumed. -/
theorem rebound_hypothetical_fullDomain (b : HilbertBasis ℕ ℂ HalfLine)
    (Omega : State b) (Szero : TraceEvolution b) (Tzero : Evolution)
    (hDiffusion : IsAbsorbingDiffusion Tzero) (hPair : IsPredual b Szero Tzero)
    (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution)
    (hReset : IsResetConstruction b Szero Omega P S T)
    (R : StandardRepresentation T) (hFull : IsFullRepresentation R) :
    (R.D : Set HalfLine) = dirichletDomain := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
