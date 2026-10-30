-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_su2_singlet
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.su2_singlet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:31:24.460982+00:00
-- url     : https://prove2.me/theorems/63128375-c650-48ab-b368-49e8ed6a567f
-- title:
--   Collective SU(2) Bose projector, (160)–(162)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   Normalized SU(2) Haar integral of U⊗U on two qubits equals the normalized singlet rank-one projector. A density matrix has Bose support under this collective action iff it equals the singlet density.
--
--   $$
--   \int_{\mathrm{SU}(2)}U\otimes U\,d\mu(U)=|\Psi^-\rangle\langle\Psi^-|,\qquad|\Psi^-\rangle=\frac{|01\rangle-|10\rangle}{\sqrt2}.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 23, Collective SU(2) Bose projector, (160)–(162)

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

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2BorelSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2BorelSpace

/-- PDF p.23, (160)–(161): SU(2), specifically, has the singlet as its unique
normalized Bose density. Its raw collective Haar projector is the singlet projector. -/
theorem su2_singlet (mu : Measure (Matrix.specialUnitaryGroup Bool ℂ))
    [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu] :
    collectiveSU2Average mu = pureDensity booleanSinglet ∧
      ∀ rho : Mat (Bool × Bool), Bose (collectiveSU2Average mu) rho ↔ rho = pureDensity booleanSinglet := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
