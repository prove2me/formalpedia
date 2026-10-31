-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P71_kernelDerivativeMultiplicity
-- name    : QAlgorithms.Papers.Independent.Intake100.P71.kernelDerivativeMultiplicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:42:26.259036+00:00
-- url     : https://prove2.me/theorems/47ed0eed-4e57-475c-aed1-619f04710f2d
-- title:
--   Zero eigenspaces have the derivative eigenvalue multiplicities
-- statement:
--   Let $H=\mathbb C^I$ with $I$ finite and nonempty, and let $\rho_0,\rho_1$ be positive definite positive density matrices of ordinary trace one. Set $d=\rho_0^{-1/2}\rho_1\rho_0^{-1/2}$. For $t\ge0$, let $P_{t,0}$ be the full orthogonal kernel projection of $\rho_1-t\rho_0$. Then
--
--   $$
--   P_{t,0}\ne0\quad\Longleftrightarrow\quad t\text{ is an eigenvalue of }d,
--   \qquad
--   \operatorname{rank} P_{t,0}=\dim_{\mathbb C}\ker(d-tI).
--   $$
--
--   The dimension is zero off the spectrum and counts multiplicity rather than distinct eigenvalues. This identifies all zero ties in the testing pencil.
-- source:
--   Quantum hypothesis testing and sufficient subalgebras, arXiv:0810.4045v2, PDF p. 9, Lemma 4: zero eigenspace and derivative multiplicities

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P71

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P71

open scoped Matrix ComplexOrder ComplexConjugate BigOperators

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Support50.P12 (Alg)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

open QAlgorithms.Papers.Independent.Bridge50.P31
  (traceConditionalExpectation stateDual algebraMultiplicativeDomain fixedPoints
   AlgebraChannel derivative weightedPair positiveTest kernelTest)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I] [nonemptyI : Nonempty I]

include nonemptyI

/-- PDF pp.9--10, Lemma 4: nonzero full kernel projection iff t is an eigenvalue
of d_(rho0,rho1), and its rank equals the COMPLEX eigenspace dimension, including
multiplicity zero off the spectrum. Threshold t=0 is included. -/
theorem kernelDerivativeMultiplicity (rho0 rho1 : Mat I)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (hf0 : rho0.PosDef) (hf1 : rho1.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    (kernelTest rho1 rho0 t ≠ 0 ↔
      ∃ v : I → ℂ, v ≠ 0 ∧ (derivative rho1 rho0) *ᵥ v = (t : ℂ) • v) ∧
    (kernelTest rho1 rho0 t).rank =
      Module.finrank ℂ (LinearMap.ker
        (derivative rho1 rho0 - (t : ℂ) • (1 : Mat I)).mulVecLin) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P71

end
