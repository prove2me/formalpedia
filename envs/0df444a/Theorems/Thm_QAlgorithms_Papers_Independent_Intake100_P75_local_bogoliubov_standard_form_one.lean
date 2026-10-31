-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_local_bogoliubov_standard_form_one
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.local_bogoliubov_standard_form_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:02:29.576287+00:00
-- url     : https://prove2.me/theorems/50215643-1a9a-48bf-81a4-8c909dc02dec
-- title:
--   Lemma 1: local Bogoliubov standard form I
-- statement:
--   Let $\rho$ be an actual normalized two-mode Gaussian density with arbitrary first moments. In the interleaved order $(x_1,p_1,x_2,p_2)$, write $M=\begin{pmatrix}G_1&C\\ C^T&G_2\end{pmatrix}$ for the full anticommutator covariance; vacuum has $M=I_4$. There are centered local linear canonical unitaries $U_1,U_2$, with active real matrices $V_1,V_2$ of determinant $1$, and real numbers $n,m,c,c'$ with $n,m\ge1$, such that the actual transformed density has covariance
--
--   $$
--   M_{\mathrm I}=(V_1\oplus V_2)M(V_1\oplus V_2)^T=
--   \begin{pmatrix}n&0&c&0\\0&n&0&c'\\c&0&m&0\\0&c'&0&m\end{pmatrix}.
--   $$
--
--   Moreover $\det G_1=n^2$, $\det G_2=m^2$, $\det C=cc'$, and $\det M=(nm-c^2)(nm-(c')^2)$. Neither correlation is required to be positive or nonzero. This normal form preserves the actual local-unitary state interpretation.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 3, Lemma 1, Eqs. (8)–(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P75

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P75

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable IsBarycenter rankOne productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl CharacteristicSummable multimodeWeylTrace
   covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Next46.P45
  (TwoMode PureVector Decomposes ladderCoefficients squeezedVector
   squeezedCoefficients GaussianShiftLaw shiftArgument)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel partialRight)

open QAlgorithms.Papers.Independent.Frontier18.P14 (occupationOutput)

open QAlgorithms.Papers.Independent.Gap48.P26 (thermalKernel)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- Lemma 1, PDF p.3, (8)--(9), including the four invariant identities at the
end of the proof. The unitaries act on the actual density, have no displacement,
and implement determinant-one active covariance matrices. Zero and either sign
of both correlations, uncorrelated products, and vacuum marginals are allowed. -/
theorem local_bogoliubov_standard_form_one
    (rho : State (FockIndex 2)) (M : Cov 2)
    (hgauss : GaussianWithCovariance rho.coefficients M) :
    ∃ (U V : AffineMultimodeGaussianUnitary 1) (n m c cprime : ℝ),
      U.displacement = 0 ∧ V.displacement = 0 ∧
      U.symplecticMatrix.det = 1 ∧ V.symplecticMatrix.det = 1 ∧
      1 ≤ n ∧ 1 ≤ m ∧
      GaussianWithCovariance
        (conjugateKernel (tensorUnitaryKernel U.unitary V.unitary) rho.coefficients)
        (standardFormCovariance n m c cprime) ∧
      standardFormCovariance n m c cprime =
        localCanonicalMatrix U V * M * (localCanonicalMatrix U V).transpose ∧
      (modeCovarianceBlock M 0 0).det = n ^ 2 ∧
      (modeCovarianceBlock M 1 1).det = m ^ 2 ∧
      (modeCovarianceBlock M 0 1).det = c * cprime ∧
      M.det = (n * m - c ^ 2) * (n * m - cprime ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
