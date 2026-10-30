-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_su2_finite_average
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.su2_finite_average
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:31:59.453692+00:00
-- url     : https://prove2.me/theorems/ead2a25e-6b56-49e8-a25e-d0ca18c40be3
-- title:
--   Twelve bilateral rotations realize the two-qubit projector
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   Define Ba=Ra(-π/2)⊗Ra(-π/2), Ra(θ)=cos(θ/2)I-i sin(θ/2)σa. For precisely the twelve products in (166), their average equals the SU(2) singlet projector, and the controlled test realizes that projector. Keep the twelve terms as the source lists them.
--
--   $$
--   \frac1{12}\sum_{i=1}^{12}U_i=|\Psi^-\rangle\langle\Psi^-|.
--   $$
--
--   With $B_a=R_a(-\pi/2)\otimes R_a(-\pi/2)$ and $R_a(\theta)=\cos(\theta/2)I-i\sin(\theta/2)\sigma_a$, the literal list is $I,B_x^2,B_y^2,B_z^2,B_xB_y,B_yB_z,B_zB_x,B_yB_x,(B_xB_y)^2,(B_yB_z)^2,(B_zB_x)^2,(B_yB_x)^2$.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 23, Twelve bilateral rotations realize the two-qubit projector

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

/-- PDF pp.23–24, (162)–(166): twelve explicit bilateral rotations average to
the same singlet projector; no direct-product group assertion is used. -/
theorem su2_finite_average :
    (12 : ℂ)⁻¹ • twelveRotations.sum = pureDensity booleanSinglet := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
