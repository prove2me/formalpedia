-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_pureState_stabilization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.pureState_stabilization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:16:42.020064+00:00
-- url     : https://prove2.me/theorems/cc49fc61-4a3b-42d2-99dd-cecbbecf6771
-- title:
--   Corollary 3.6: Pure-state stabilizability
-- statement:
--   For $n\ge2$ and a GKSL generator $G=-L$, the following are equivalent: some, equivalently every, simplex vertex is stabilizable; some, equivalently every, vertex is strongly stabilizable; some, equivalently every, representation of $G$ has a common jump eigenvector; and a constant Hermitian control makes some pure density stationary.
--
--   Moreover, let $\|\psi\|=1$ and $V_k\psi=z_k\psi$. For any $a\in\mathbb R$, every Hermitian $H_\psi$ satisfying
--
--   $$H_\psi\psi=-\left(H_0+\left(a-\frac1{2i}\sum_k|z_k|^2\right)I+\frac1{2i}\sum_kV_k^*V_k\right)\psi$$
--
--   makes $|\psi\rangle\langle\psi|$ stationary for $G-i[H_\psi,\cdot]$. This is stationarity; neither uniqueness nor attraction is asserted.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 10, Corollary 3.6: Pure-state stabilizability

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.10, Corollary 3.6: Pure-state stabilizability. PDF p.10 rendered: the leading minus applies to the entire parenthesized matrix. Normalization is also explicit in the moreover clause; common left eigenvectors are allowed. -/
theorem pureState_stabilization {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    List.TFAE [
      (∃ i : Fin n, stabilizable D (vertex i)),
      (∀ i : Fin n, stabilizable D (vertex i)),
      (∃ i : Fin n, stronglyStabilizable D (vertex i)),
      (∀ i : Fin n, stronglyStabilizable D (vertex i)),
      someRepresentation D (fun E => ∃ psi, commonEigenvector E.jump psi),
      everyRepresentation D (fun E => ∃ psi, commonEigenvector E.jump psi),
      (∃ (H : Mat n) (hH : H.IsHermitian) (psi : Hilbert n),
        ‖psi‖ = 1 ∧ stationary (controlledData D H hH) (QAlgorithms.pureDensity psi))] ∧
    (∀ (psi : Hilbert n), ‖psi‖ = 1 → ∀ z : Fin D.count → ℂ,
      (∀ k, QAlgorithms.act (D.jump k) psi = z k • psi) →
      ∀ (a : ℝ) (H : Mat n) (hH : H.IsHermitian),
      QAlgorithms.act H psi = QAlgorithms.act (pureHamiltonianRHS D z a) psi →
      stationary (controlledData D H hH) (QAlgorithms.pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
