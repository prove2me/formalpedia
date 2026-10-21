-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_transport_flux_independence
-- name    : QAlgorithms.Papers.Independent.Next46.P23.transport_flux_independence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:58:25.631273+00:00
-- url     : https://prove2.me/theorems/b54c663d-c5e0-4b37-bb9d-2129d48a01f3
-- title:
--   Proposition 3.13
-- statement:
--   For two continuously differentiable flux relations $\Phi_X,\widetilde\Phi_X$ for the SAME nonzero finite-dimensional family $H_X,\omega_X$, with equilibrium invariant and states faithful and normalized, define finite-time coefficients by differentiating time-averaged current means at zero force. For $t>0$, $$L^t_{jk}+L^t_{kj}=\widetilde L^t_{jk}+\widetilde L^t_{kj}.$$ If both descriptions satisfy the finite-time Onsager reciprocity relations, their coefficients themselves agree. No uniqueness of flux decomposition is assumed.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 88, Proposition 3.13

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Proposition3.13, source PDF p.88: symmetric parts agree for two flux relations.
Equality of coefficients requires ORR for both descriptions. -/
theorem transport_flux_independence [Nonempty I] {n : ℕ} (F G : FluxFamily I n)
    (hF : FluxC1 F) (hG : FluxC1 G) (hH : F.H = G.H) (homega : F.omega = G.omega)
    (t : ℝ) (ht : 0 < t) :
    (∀ j k, kineticCoefficient F t j k + kineticCoefficient F t k j = kineticCoefficient G t j k + kineticCoefficient G t k j) ∧
    ((∀ j k, kineticCoefficient F t j k = kineticCoefficient F t k j) →
      (∀ j k, kineticCoefficient G t j k = kineticCoefficient G t k j) →
        ∀ j k, kineticCoefficient F t j k = kineticCoefficient G t j k) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
