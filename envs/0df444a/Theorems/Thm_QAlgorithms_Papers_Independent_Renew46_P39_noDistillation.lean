-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_noDistillation
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.noDistillation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:13:38.414397+00:00
-- url     : https://prove2.me/theorems/214398f8-f158-4d1f-99ce-a2d3f4af8f87
-- title:
--   Two-copy Gaussian no-distillation under the restricted Fig.1 protocol
-- statement:
--   Let $\rho$ be a normalized Gaussian density operator on the full two-oscillator Hilbert space, with arbitrary first moments and covariance
--   $$\Gamma_0=\begin{pmatrix}aI_2&cZ\\cZ&aI_2\end{pmatrix},\qquad Z=\operatorname{diag}(1,-1),\quad a\ge1,\quad 0\le c\le\sqrt{a^2-1}.$$
--   Covariances use $[X,P]=i$ and vacuum covariance $I$. Prepare two independent copies, ordered $A_1,A_2,B_1,B_2$. Alice and Bob independently apply arbitrary local two-mode Gaussian unitaries, including displacements, corresponding to real symplectic matrices $S_A,S_B\in\mathrm{Sp}(4,\mathbb R)$. They measure $P$ on $A_2,B_2$, communicate both real outcomes, and may apply measurable outcome-dependent local Gaussian unitary feedback on $A_1,B_1$. Local quadrature rotations include other homodyne angles.
--
--   Every finite outcome has a normalized conditional density. For every such conditional density, the final density $\tau$ after feedback is Gaussian, and both $\rho^{T_A}$ and $\tau^{T_A}$ are trace class with finite trace norm at least one. With partial transpose on Alice and $E_N(\omega)=\log_2\|\omega^{T_A}\|_1$,
--   $$E_N(\tau)\le E_N(\rho).$$
--   This compares the output with one input pair. It excludes added modes and other measurements, and makes no general Gaussian-LOCC no-go claim.
--
--   **Formalization Note** Homodyne outcomes are trace-norm limits of actual normalized displaced pure-Gaussian projections. Their covariance update and the finiteness of partial-transpose trace norms are conclusions, not premises.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 2, Theorem (p.2); restricted two-copy Gaussian no-distillation result announced p.1

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

/-- PDF p.2, Theorem, with Fig.1 feedback from p.1 and displacements [7].
For every finite selective outcome compare the output to ONE input copy.
The actual densities and finite partial-transpose trace norms are established,
not replaced by the Schur expression or assumed log-negativity inequalities.
Base 2 and the p.2 Eq.(4) normalization take precedence over the missing half
in the p.3 proof. -/
theorem noDistillation (rho : DensityKernel 2) (a c : ℝ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hca : c ≤ Real.sqrt (a ^ 2 - 1))
    (hrho : GaussianWithCovariance rho (initialCovariance a c)) (p : TwoCopyHomodyneProtocol) :
    FinitePartialTranspose rho ∧
    (∀ y : Outcome, ∃ sigma : DensityKernel 2,
      HomodyneOutcome (beforeMeasurement p rho) y sigma) ∧
    (∀ (y : Outcome) (sigma : DensityKernel 2),
      HomodyneOutcome (beforeMeasurement p rho) y sigma →
      (∃ gammaOut : Cov 2, GaussianWithCovariance (afterFeedback p y sigma) gammaOut) ∧
      FinitePartialTranspose (afterFeedback p y sigma) ∧
      oscillatorLogNegativity (afterFeedback p y sigma) ≤ oscillatorLogNegativity rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
