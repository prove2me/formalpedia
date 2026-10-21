-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_dynamics_inner
-- name    : QAlgorithms.Papers.Independent.Next46.P23.dynamics_inner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:40:01.744506+00:00
-- url     : https://prove2.me/theorems/80bf7a1a-bc8a-40c5-b2ef-a43a213e7f64
-- title:
--   §2.8: every finite-dimensional dynamics is Hamiltonian
-- statement:
--   Every continuous one-parameter group $\tau^t$ of complex-linear star-automorphisms of $B(K)$, with $K$ nonzero and finite-dimensional, has a self-adjoint Hamiltonian $H$ such that $$\tau^t(A)=e^{itH}Ae^{-itH}\quad(t\in\mathbb R).$$ Any other self-adjoint Hamiltonian implementing the same group differs from $H$ by a real scalar multiple of the identity. The erroneous nearby simply-connectedness remark is not included.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 52, §2.8: every finite-dimensional dynamics is Hamiltonian

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

/-- Every finite dynamics is Hamiltonian, uniquely up to a real scalar; source PDF p.52. -/
theorem dynamics_inner [Nonempty I] (T : ℝ → Mat I →ₗ[ℂ] Mat I) (hT : AutomorphismDynamics T) :
    ∃ H : Mat I, H.IsHermitian ∧ (∀ t A, T t A = tau H t A) ∧
      ∀ G : Mat I, G.IsHermitian → (∀ t A, T t A = tau G t A) →
        ∃ c : ℝ, G = H + (c : ℂ) • 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
