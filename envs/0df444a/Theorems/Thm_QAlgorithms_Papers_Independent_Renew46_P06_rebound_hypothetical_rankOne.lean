-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_rebound_hypothetical_rankOne
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.rebound_hypothetical_rankOne
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:50:24.053274+00:00
-- url     : https://prove2.me/theorems/6b644598-994f-427d-b10e-8b2d2cac2dcc
-- title:
--   A hypothetical standard rebound representation has the same rank-one generator values
-- statement:
--   Fix any rebound density $\Omega$ on $H=L^2(\mathbb R_+)$. Let $G_0$ be the actual absorbing diffusion generator and $G$ the generator of its actual minimal reset construction. Assume, only in this contradiction lemma, that the reset dual admits a standard representation with maximal accretive Hilbert operator $K$ on its full closed domain and countably many jumps satisfying the dissipativity inequality.
--
--   For every $\psi,\varphi\in\operatorname{dom}K$, put $\rho=|\psi\rangle\langle\varphi|$. Then
--
--   $$
--   \rho\in\operatorname{dom}G\cap\operatorname{dom}G_0,
--   \qquad G\rho=G_0\rho.
--   $$
--
--   In graph form there exists the same trace-class value $\eta$ with $(\rho,\eta)$ in both actual generator graphs. Zero factors are allowed.
--
--   The conclusion expresses vanishing of reset on the hypothetical representation's rank-one tests; it does not assume the regularity or domain equality established by the neighboring lemmas.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 9, Lemma 6: hypothetical standard representation has zero reset on rank-one tests

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

/-- PDF p.9, Lemma 6: ONLY this contradiction lemma assumes a hypothetical full-domain
standard realization. The same actual generator value belongs to both full graphs,
including when a rank-one factor is zero. -/
theorem rebound_hypothetical_rankOne (b : HilbertBasis ℕ ℂ HalfLine)
    (Omega : State b) (Szero : TraceEvolution b) (Tzero : Evolution)
    (hDiffusion : IsAbsorbingDiffusion Tzero) (hPair : IsPredual b Szero Tzero)
    (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution)
    (hReset : IsResetConstruction b Szero Omega P S T)
    (R : StandardRepresentation T) (hFull : IsFullRepresentation R)
    (f g : R.D) (rho : (TraceClass HalfLine))
    (hRankOne : rho.val = InnerProductSpace.rankOne ℂ (f : HalfLine) (g : HalfLine)) :
    ∃ eta : (TraceClass HalfLine),
      InTraceGeneratorGraph S rho eta ∧ InTraceGeneratorGraph Szero rho eta := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
