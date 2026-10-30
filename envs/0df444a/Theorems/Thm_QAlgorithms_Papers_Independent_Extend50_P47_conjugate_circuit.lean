-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_conjugate_circuit
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.conjugate_circuit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:16:45.646046+00:00
-- url     : https://prove2.me/theorems/cf25f34a-cefc-49bb-b90f-b9c07134fb3d
-- title:
--   Conjugate representation circuit by gate replacement
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   For every fixed circuit over CNOT, H, T, replacing each T by T† and preserving gate order and wires implements the entrywise complex conjugate of the original circuit unitary.
--
--   $$
--   U(\overline C)=\overline{U(C)},\qquad|\overline C|=|C|.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 5, Conjugate representation circuit by gate replacement

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF p.5: exact conjugate circuit by gate replacement, with unchanged size.
The input circuit uses the paper's H,CNOT,T gate set. -/
theorem conjugate_circuit {n : ℕ} (c : List (StandardStep n))
    (hc : ∀ q, StandardStep.td q ∉ c) :
    standardCircuit (c.map conjugateStep) = (standardCircuit c).map conj ∧
      (c.map conjugateStep).length = c.length := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
