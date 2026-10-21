-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_shiftDual_nonunitalStarDomain
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.shiftDual_nonunitalStarDomain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:47:41.991655+00:00
-- url     : https://prove2.me/theorems/dbc09ec9-af80-4676-9d03-9a794929603e
-- title:
--   The unperturbed shift dual-generator domain is a nonunital star algebra
-- statement:
--   Let $W_t f(x)=f(x+t)$ on $H=L^2(\mathbb R_+)$ and $T_t^0(X)=W_t^*XW_t$. Let $\mathcal L_0$ be the full ultraweak generator, defined through all trace-class pairings. Then
--
--   $$
--   \operatorname{dom}\mathcal L_0\text{ is closed under complex linear combinations, adjoints and products},
--   \qquad I\notin\operatorname{dom}\mathcal L_0.
--   $$
--
--   In particular, zero belongs to the domain, sums and complex multiples stay in it, and $X,Y$ in the domain imply $X^*$ and $XY$ are in the domain. This is an algebra without an identity requirement; the generator is not an operator-norm generator.
--
--   The exclusion of the identity is the feature used in the paper's domain-algebra argument.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 5, Lemma 3: the shift dual-generator domain is a nonunital star algebra

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

/-- PDF p.5, Lemma 3: complex linear, adjoint and multiplicative closure together
with exclusion of I; this is a nonunital star algebra, not a StarSubalgebra. -/
theorem shiftDual_nonunitalStarDomain (b : HilbertBasis ℕ ℂ HalfLine)
    (W : ContractionSemigroup HalfLine) (hShift : IsLeftShift W)
    (Szero : TraceEvolution b) (Tzero : Evolution) (hPair : IsShiftPair b W Szero Tzero) :
    IsNonunitalStarDomain (dualGeneratorDomain b Tzero) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
