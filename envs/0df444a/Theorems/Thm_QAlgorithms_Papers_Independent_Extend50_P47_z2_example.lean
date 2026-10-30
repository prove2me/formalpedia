-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_z2_example
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.z2_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:30:36.684343+00:00
-- url     : https://prove2.me/theorems/e3a14693-4489-4937-90b4-1e6e004ebc50
-- title:
--   Z2 analytic symmetry example
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For U(e)=I,U(g)=Pauli Z on one qubit, Π=|0⟩⟨0|; Bose symmetry means ρ=|0⟩⟨0|, while conjugation symmetry means ρ is diagonal in the computational basis.
--
--   $$
--   \Pi=\frac{I+Z}{2}=|0\rangle\langle0|,\qquad p_{\rm acc}(\rho)=\rho_{00},\qquad\rho\in\mathrm{B\!\text{-}Sym}\iff\rho=|0\rangle\langle0|.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 20, Z2 analytic symmetry example

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

/-- PDF p.20, Z2 example: the analytic projector and its exact test. -/
theorem z2_example :
    ((1 / 2 : ℂ) • ((1 : Mat Bool) + pauliZ)) = Matrix.single false false 1 ∧
    ∀ rho : Mat Bool, IsDensityMatrix rho →
      controlReturnProbability ((1 / 2 : ℂ) • ((1 : Mat Bool) + pauliZ)) rho = (rho false false).re ∧
      (Bose ((1 / 2 : ℂ) • ((1 : Mat Bool) + pauliZ)) rho ↔
        rho = Matrix.single false false 1) ∧
      (Sym (fun g : Bool => if g then pauliZ else 1) rho ↔
        ∀ i j, i ≠ j → rho i j = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
