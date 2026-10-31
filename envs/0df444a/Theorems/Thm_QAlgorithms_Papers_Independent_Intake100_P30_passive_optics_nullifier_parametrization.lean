-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_passive_optics_nullifier_parametrization
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.passive_optics_nullifier_parametrization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:56:07.574455+00:00
-- url     : https://prove2.me/theorems/f67944a1-f461-4ffb-8afe-bdb82828c540
-- title:
--   Appendix C: stabilizer/nullifier construction from passive optics
-- statement:
--   Let $r_j$ be real squeezing parameters, $D=\operatorname{diag}(e^{-2r_j})$, and let $L=X+iY$ be a complex unitary matrix with real $X,Y$. In the passive stabilizer conjugation convention of Appendix C, put
--
--   $$A=X+iDY,\qquad B=iDX-Y,\qquad Z=A^{-1}B.$$
--
--   Then $A$ is invertible, $Z$ is a valid Gaussian graph, and the corresponding actual Gaussian wavefunction is annihilated by $Ap-Bq$. Conversely, every valid $n$-mode graph has such parameters. Multiplication by $D$ is on the left. The passive conjugation is the inverse of the forward Heisenberg convention used for state evolution; no uniqueness of the parameters is asserted.
--
--   There exists an actual Gaussian unitary with forward Heisenberg matrix $\begin{psmallmatrix}X^T&Y^T\\-Y^T&X^T\end{psmallmatrix}$, the inverse of (C12), which sends every normalized squeezed-input state with graph $iD$ to a state represented by $Z$. This ties the coefficient calculation to the prepared state.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 23, Appendix C: stabilizer/nullifier construction from passive optics

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.23–24, (C13)–(C17): left-row squeezing and passive
stabilizer conjugation give Z=A^{-1}B; the inverse conjugation convention is
retained rather than replaced by the forward state-evolution convention.
The passive Gaussian unitary is asserted to exist and sends every squeezed-input
representative to the graph A^{-1}B. Its Heisenberg matrix is the inverse of
(C12), namely [[X^T,Y^T],[-Y^T,X^T]], since (C11) conjugates operators by U.
Every allowed graph is covered; parameters need not be independent or unique. -/
theorem passive_optics_nullifier_parametrization (n : ℕ) :
    (∀ (r : Fin n → ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ),
      (complexify X + Complex.I • complexify Y).conjTranspose *
        (complexify X + Complex.I • complexify Y) = 1 →
      let A := passiveA r X Y
      let B := passiveB r X Y
      let Z := A⁻¹ * B
      IsUnit A.det ∧ ValidGraph Z ∧
      (∃ Uop : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n,
        IsImplementer (Matrix.fromBlocks X.transpose Y.transpose (-Y.transpose) X.transpose) Uop ∧
        ∀ psi : Schrodinger n,
          GaussianGraphRepresents
            (Complex.I • complexify (Matrix.diagonal (fun j => Real.exp (-2*r j)))) psi →
          GaussianGraphRepresents Z (Uop psi)) ∧
      (∀ j q,
        let f := gaussianWave (imagPart Z) (-realPart Z)
        (∑ k, A j k * quadratureFunction (Sum.inr k) f q) -
          (∑ k, B j k * quadratureFunction (Sum.inl k) f q) = 0)) ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℂ, ValidGraph Z →
      ∃ (r : Fin n → ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ),
        (complexify X + Complex.I • complexify Y).conjTranspose *
          (complexify X + Complex.I • complexify Y) = 1 ∧
        Z = (passiveA r X Y)⁻¹ * passiveB r X Y) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
