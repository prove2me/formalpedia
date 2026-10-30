-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_u2_zero_projector
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.u2_zero_projector
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:32:46.06885+00:00
-- url     : https://prove2.me/theorems/6743942b-9577-44d5-9a0f-156b86b08d95
-- title:
--   Collective U(2) Bose projector vanishes, (171)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   Normalized U(2) Haar average of U⊗U is zero. Its conjugation twirl is the same as the SU(2) collective conjugation twirl, although its Bose test always rejects.
--
--   $$
--   \int_{\mathrm U(2)}U\otimes U\,d\mu(U)=0,\qquad p_{\rm acc}(\rho)=0.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 24, Collective U(2) Bose projector vanishes, (171)

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

/-- PDF p.24, (171): the normalized U(2) Haar Bose average vanishes. -/
theorem u2_zero_projector (mu : Measure (Matrix.unitaryGroup Bool ℂ))
    [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu] :
    (∫ U, Matrix.kronecker (U : Mat Bool) (U : Mat Bool) ∂mu) = 0 ∧
    ∀ rho : Mat (Bool × Bool), IsDensityMatrix rho →
      controlReturnProbability (∫ U, Matrix.kronecker (U : Mat Bool) (U : Mat Bool) ∂mu) rho = 0 ∧
      ∀ nu : Measure (Matrix.specialUnitaryGroup Bool ℂ),
        Measure.IsHaarMeasure nu → IsProbabilityMeasure nu →
        (∫ U, (Matrix.kronecker (U : Mat Bool) (U : Mat Bool)) * rho *
          (Matrix.kronecker (U : Mat Bool) (U : Mat Bool))ᴴ ∂mu) =
        (∫ U, (Matrix.kronecker (U : Mat Bool) (U : Mat Bool)) * rho *
          (Matrix.kronecker (U : Mat Bool) (U : Mat Bool))ᴴ ∂nu) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
