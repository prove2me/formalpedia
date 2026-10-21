-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_homodyneLimit
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.homodyneLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:16:54.126752+00:00
-- url     : https://prove2.me/theorems/e7f474e3-069a-4e45-9150-6474347793ee
-- title:
--   Ideal homodyne covariance and the positive-parameter Schur limit
-- statement:
--   Let $\rho'$ be an arbitrary normalized four-mode Gaussian density with covariance $\Gamma'$, arbitrary first moments, and retained/discarded blocks $C_1,C_2,C_3$ in the order $(A_1,B_1;A_2,B_2)$. For $d>0$, let
--   $$V_d=\operatorname{diag}(d^{-2},d^2,d^{-2},d^2),\qquad M_d=C_1-C_3(C_2+V_d)^{-1}C_3^T.$$
--   Put $\pi_P=\operatorname{diag}(0,1,0,1)$, and denote the Moore–Penrose inverse by a superscript $+$.
--
--   Every finite pair of $P$-homodyne outcomes on $A_2,B_2$ has a normalized conditional density on $A_1,B_1$. Every such density is Gaussian with the same covariance, independent of its outcome and initial first moments:
--   $$\Gamma''=C_1-C_3(\pi_PC_2\pi_P)^+C_3^T,\qquad \lim_{d\to0^+}M_d=\Gamma''.$$
--   This gives both the operational covariance identification and convergence of the finite-seed expressions.
--
--   **Formalization Note** Ideal conditional densities are defined by trace-norm limits of normalized pure seeds centered at the measured momenta. With this $d\to0^+$ family the printed $\operatorname{diag}(1,0,1,0)$ is corrected to $\pi_P$; measuring $X$ instead requires the opposite squeezing limit or a local rotation.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 3, Lemma 2: ideal homodyne limit and Moore-Penrose formula

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

/-- PDF p.3, Lemma 2, corrected: the finite seed V_d of Lemma 1 and d->0+
select P, so piP=diag(0,1,0,1), replacing printed piX. Gamma_d means M_d,
not the 8-by-8 augmented matrix. This asserts existence and identification of
all finite-outcome actual conditional states AND convergence of covariances. -/
theorem homodyneLimit (rho : DensityKernel 4) (gamma : Cov 4)
    (hrho : GaussianWithCovariance rho gamma) :
    Tendsto (fun d : ℝ => finiteSchur gamma d) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (homodyneCovariance gamma)) ∧
    (∀ y : Outcome, ∃ sigma : DensityKernel 2, HomodyneOutcome rho y sigma) ∧
    (∀ (y : Outcome) (sigma : DensityKernel 2), HomodyneOutcome rho y sigma →
      GaussianWithCovariance sigma (homodyneCovariance gamma)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
