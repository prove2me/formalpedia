-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_lazySubspace_stabilizingHamiltonian
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.lazySubspace_stabilizingHamiltonian
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:42:05.745976+00:00
-- url     : https://prove2.me/theorems/c738d8e6-7e86-4657-aa06-46bee548a856
-- title:
--   Corollary C.11: A constant Hamiltonian makes every lazy subspace collecting
-- statement:
--   For a GKSL generator $G=-L$ and a nonzero lazy subspace $S$ with orthogonal projection $P$, there is a Hermitian $H_S$ making $S$ collecting for $G-i[H_S,\cdot]$. Every Hermitian $H_S$ satisfying
--
--   $$P^\perp H_SP=-P^\perp\left(H_0+\frac1{2i}\sum_kV_k^*V_k\right)P$$
--
--   has this property, and such a Hermitian matrix exists. The result provides a constant stabilizing Hamiltonian, with no assertion of unique stationarity or attraction.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 33, Corollary C.11: A constant Hamiltonian makes every lazy subspace collecting

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

/-- arXiv:2308.00561v1, PDF p.33, Corollary C.11: A constant Hamiltonian makes every lazy subspace collecting. Correction (trap 30): PDF p.33 prints G+i ad_HS, but the printed block condition and the p.10 applications require G-i ad_HS. The rendered block formula uses 1/(2i); Remark C.4 has a separate printed sign error, corrected in shiftedDriftHamiltonian. -/
theorem lazySubspace_stabilizingHamiltonian {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (S : Submodule ℂ (Hilbert n)) (hS : lazy D.jump S) :
    (∃ (H : Mat n) (hH : H.IsHermitian), stabilizingBlock D S H ∧
      collecting (driftK (controlledData D H hH)) D.jump S) ∧
    (∀ (H : Mat n) (hH : H.IsHermitian), stabilizingBlock D S H →
      collecting (driftK (controlledData D H hH)) D.jump S) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
