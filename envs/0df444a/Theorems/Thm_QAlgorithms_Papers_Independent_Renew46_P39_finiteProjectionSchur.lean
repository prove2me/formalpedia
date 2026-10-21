-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_finiteProjectionSchur
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.finiteProjectionSchur
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:16:22.69558+00:00
-- url     : https://prove2.me/theorems/70dbda9a-ccb0-42ed-b8e9-f2d9e3f03db1
-- title:
--   Finite pure-Gaussian projection gives the Schur complement
-- statement:
--   Let $\rho'$ be any normalized four-mode Gaussian density on $A_1,A_2,B_1,B_2$, with arbitrary first moments. Reorder the interleaved quadratures into the retained/discarded split $(A_1,B_1;A_2,B_2)$, and write its covariance as
--   $$\Gamma'=\begin{pmatrix}C_1&C_3\\C_3^T&C_2\end{pmatrix},\qquad C_j\in\mathbb R^{4\times4}.$$
--   For $d>0$, project the discarded modes on a normalized pure Gaussian seed of arbitrary means and covariance
--   $$V_d=\operatorname{diag}(d^{-2},d^2,d^{-2},d^2).$$
--   The coefficient contraction and trace series converge, the projection weight is positive, and normalizing the actual projected density yields a Gaussian state on $A_1,B_1$ with covariance
--   $$M_d=C_1-C_3(C_2+V_d)^{-1}C_3^T.$$
--   This identifies the covariance of an actual selective quantum projection for a general four-mode Gaussian input; no two-copy assumption is imposed.
--
--   **Formalization Note** The printed lemma calls $D_d=\operatorname{diag}(d^{-1},d,d^{-1},d)$ the seed covariance but uses $D_d^2$ throughout its integral and update. The statement follows that proof by using the seed covariance $V_d=D_d^2$. The original quotation is retained separately.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 2, Lemma 1: finite pure-Gaussian projection and Schur complement

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39

noncomputable section

open Filter

open scoped BigOperators Topology ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P39

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsTraceClass traceSize rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl weylArgument CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm isSymplectic)

open QAlgorithms.Papers.Independent.Dependency50.P10
  (physicalCovariance supportInverse)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)

/-- PDF p.2, Lemma 1 and (7)--(9), corrected: printed D_d is called a
covariance but squared in the integral and Schur formula. Here the seed has
V_d=diag(d^-2,d^2,d^-2,d^2), following the proof. Both block permutation and
actual normalized projection are explicit; gamma is an arbitrary four-mode
Gaussian covariance, without the theorem's two-copy restriction. -/
theorem finiteProjectionSchur (rho : DensityKernel 4) (gamma : Cov 4)
    (hrho : GaussianWithCovariance rho gamma) (d : ℝ) (hd : 0 < d)
    (seed : DensityKernel 2) (hseed : PureSeed d seed) :
    ProjectionSummable rho seed ∧ 0 < projectionWeight rho seed ∧
    GaussianWithCovariance (finiteOutput rho seed) (finiteSchur gamma d) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
