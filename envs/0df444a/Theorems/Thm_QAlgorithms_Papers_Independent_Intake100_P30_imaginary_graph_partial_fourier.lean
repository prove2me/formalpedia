-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_imaginary_graph_partial_fourier
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.imaginary_graph_partial_fourier
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:48:05.288281+00:00
-- url     : https://prove2.me/theorems/1afe89d7-9fba-43c7-9770-615871a263b6
-- title:
--   IV.B: partial Fourier transform of an H-graph and stationarity
-- statement:
--   Let $U=\begin{psmallmatrix}U_1&U_2^T\\U_2&U_3\end{psmallmatrix}>0$ be real symmetric. For $Z=iU$, Fourier transforming the first block gives a valid graph, $U_1$ is invertible, and
--
--   $$Z'=\begin{pmatrix}iU_1^{-1}&-U_1^{-1}U_2^T\\-U_2U_1^{-1}&i(U_3-U_2U_1^{-1}U_2^T)\end{pmatrix}.$$
--
--   The phase-error derivative vanishes at $Z'$. More generally, applying any integer multiples of $\pi/2$ on any modes of $iU$ gives $\operatorname{diag}(\operatorname{Im}Z'\operatorname{Re}Z')=0$ and hence stationarity. Empty selected blocks and selection of all modes are included.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 14, IV.B: partial Fourier transform of an H-graph and stationarity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.14, (4.6): partial Fourier formula and stationarity after
any integer quarter-turns on an imaginary graph. Empty/all selected blocks
are included; U1 invertibility is derived, never assumed. The printed word
"extremum" is read as stationarity, following the vanishing-first-derivative
calculation in Appendix B; that calculation does not establish a minimum. -/
theorem imaginary_graph_partial_fourier {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U1 : Matrix I I ℝ) (U2 : Matrix J I ℝ)
    (U3 : Matrix J J ℝ) (hU : (Matrix.fromBlocks U1 U2.transpose U2 U3).PosDef) :
    let Z := Complex.I • complexify (Matrix.fromBlocks U1 U2.transpose U2 U3)
    let Zp := graphLocalMobius 0 (-1) 1 0 Z
    IsUnit U1.det ∧ ValidGraph Zp ∧
    Zp = Matrix.fromBlocks (Complex.I • complexify U1⁻¹)
      (-complexify (U1⁻¹ * U2.transpose)) (-complexify (U2 * U1⁻¹))
      (Complex.I • complexify (U3 - U2 * U1⁻¹ * U2.transpose)) ∧
    HasFDerivAt (phaseError Zp) (0 : (I ⊕ J → ℝ) →L[ℝ] ℝ) 0 ∧
    (∀ k : I ⊕ J → ℤ,
      let H := graphPhaseMobius Z (fun j => (k j : ℝ) * Real.pi / 2)
      (∀ j, (imagPart H * realPart H) j j = 0) ∧
      HasFDerivAt (phaseError H) (0 : (I ⊕ J → ℝ) →L[ℝ] ℝ) 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
