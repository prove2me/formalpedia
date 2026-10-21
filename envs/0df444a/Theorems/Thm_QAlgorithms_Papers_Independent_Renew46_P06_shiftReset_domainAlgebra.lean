-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_shiftReset_domainAlgebra
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.shiftReset_domainAlgebra
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:46:47.049589+00:00
-- url     : https://prove2.me/theorems/09a852e7-390a-4ee4-be11-951927bf25a8
-- title:
--   The shift-reset domain algebra annihilates centered observables on the rebound support
-- statement:
--   Let $\Omega$ be any density operator on $H=L^2(\mathbb R_+)$, and let $T$ be the normal dual of the actual minimal rank-one reset of the left-shift predual semigroup. Let $\mathcal L$ be its ultraweak generator and set
--
--   $$
--   \mathcal A=\{X\in\operatorname{dom}\mathcal L:
--   X^*X,XX^*\in\operatorname{dom}\mathcal L\}.
--   $$
--
--   For every $X\in\mathcal A$, with $c=\operatorname{Tr}(\Omega X)$, both products vanish:
--
--   $$
--   (X-cI)\Omega=0,\qquad \Omega(X-cI)=0.
--   $$
--
--   If $\Omega$ is injective, then $\mathcal A=\{cI:c\in\mathbb C\}$. Injectivity is faithfulness of the density, not bounded invertibility.
--
--   The two annihilation identities locate the algebra on the support of the rebound state and yield an evolution whose domain algebra is exactly the scalar algebra.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 4, Theorem 2: domain algebra annihilates the centered observable on the support of Omega

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

/-- PDF pp.4,6, Theorem 2: both annihilating products, followed by equality with the
scalar algebra for injective Omega. Injectivity does not mean a bounded inverse. -/
theorem shiftReset_domainAlgebra (b : HilbertBasis ℕ ℂ HalfLine)
    (Omega : State b) (W : ContractionSemigroup HalfLine) (hShift : IsLeftShift W)
    (Szero : TraceEvolution b) (Tzero : Evolution) (hPair : IsShiftPair b W Szero Tzero)
    (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution)
    (hReset : IsResetConstruction b Szero Omega P S T) :
    (∀ X ∈ domainAlgebra b T,
      (X - operatorTrace b (Omega.val.val.comp X) • identityObservable).comp Omega.val.val = 0 ∧
      Omega.val.val.comp (X - operatorTrace b (Omega.val.val.comp X) • identityObservable) = 0) ∧
    (Function.Injective Omega.val.val →
      domainAlgebra b T = {X | ∃ c : ℂ, X = c • identityObservable}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
