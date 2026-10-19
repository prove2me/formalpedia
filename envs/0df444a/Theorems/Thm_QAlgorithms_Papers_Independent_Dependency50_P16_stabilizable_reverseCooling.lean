-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_stabilizable_reverseCooling
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.stabilizable_reverseCooling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:30:33.477057+00:00
-- url     : https://prove2.me/theorems/129d6b43-8d48-4462-a062-71a66894042a
-- title:
--   Corollary 4.22: Reverse cooling in stabilizable systems
-- statement:
--   Let a GKSL reduced system on $\mathbb C^n$, $n\ge2$, be stabilizable. If it has a complex two-dimensional lazy subspace on which the dissipative jump restrictions are not all scalar, then
--
--   $$\text{the reduced system is reverse coolable}.$$
--
--   The non-Hamiltonian condition is on the dissipation after a stabilizing Hamiltonian makes the lazy subspace collecting. It is independent of the freely chosen Hamiltonian.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 22, Corollary 4.22: Reverse cooling in stabilizable systems

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

/-- arXiv:2308.00561v1, PDF p.22, Corollary 4.22: Reverse cooling in stabilizable systems. Two-dimensional means complex subspace dimension two, not face dimension two. Scalar restrictions are tested on the entire lazy subspace. -/
theorem stabilizable_reverseCooling {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (i0 : Fin n) (hi0 : i0.val = 0) (h : stabilizableSystem D)
    (hS : ∃ S : Submodule ℂ (Hilbert n), lazy D.jump S ∧ Module.finrank ℂ S = 2 ∧
      ¬(∀ k, scalarOn (D.jump k) S)) : reverseCoolable D i0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
