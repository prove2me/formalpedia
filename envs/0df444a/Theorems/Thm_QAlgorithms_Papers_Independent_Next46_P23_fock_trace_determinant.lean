-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_fock_trace_determinant
-- name    : QAlgorithms.Papers.Independent.Next46.P23.fock_trace_determinant
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:00:58.194955+00:00
-- url     : https://prove2.me/theorems/ba5980bf-66f5-42f4-8508-35d1d5a5550b
-- title:
--   Lemma 6.1
-- statement:
--   Let $K$ be any finite-dimensional complex Hilbert space and $A\in B(K)$. With fermionic Fock space including its vacuum sector and $\Gamma(A)=\bigoplus_{r=0}^{\dim K}\wedge^rA$, $$\operatorname{tr}_{\Gamma(K)}\Gamma(A)=\det_K(I+A).$$ No positivity or self-adjointness is required. Occupation-basis minors implement the actual exterior powers; for $K=0$ both sides are one.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 118, Lemma 6.1

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

/-- Lemma6.1, source PDF p.118. The vacuum contributes one even when n=0. -/
theorem fock_trace_determinant (n : ℕ) (A : Mat (Fin n)) :
    (fockGamma A).trace = Matrix.det (1+A) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
