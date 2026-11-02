-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_theorem5_unknown_projector
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.theorem5_unknown_projector
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:04:05.489416+00:00
-- url     : https://prove2.me/theorems/4e6fbdd3-ea02-4d12-b1a6-4df0c60aa678
-- title:
--   Theorem 5: unknown-projector outcome and nondisturbance bounds
-- statement:
--   Take any finite nonempty family of unit sample vectors, with arbitrary overlaps and dependencies. Let $\Pi$ project onto their span, $\sigma_{\rm avg}=K^{-1}\sum_k|\phi_k\rangle\langle\phi_k|$, and $\lambda_{\min}$ its minimum strictly positive eigenvalue. Use the Fig.7 history of $T\ge0$ independent uniform sample reflections, measure all-minus versus its complement, undo the same history, and let $\mathcal E_T$ ignore the outcome. The positive spectral support is nonempty and $0<\lambda_{\min}\le1$. For every density input,
--
--   $$\operatorname{Tr}(\Pi\rho)-(1-\lambda_{\min})^T\le\Pr(b=0)\le\operatorname{Tr}(\Pi\rho).$$
--
--   If $[\Pi,\rho]=0$, then also
--
--   $$F(\mathcal E_T(\rho),\rho)\ge1-(1-\lambda_{\min})^T.$$
--
--   Here $b=0$ is span detection and $b=1$ is all-minus. No algebra-generation promise is used.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 32, Theorem 5: unknown-projector outcome and nondisturbance bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.32–34, Theorem 5: both probability and fidelity clauses. The commutation
hypothesis belongs only to fidelity; minPositiveEigenvalue excludes ambient zeros. -/
theorem theorem5_unknown_projector [Nonempty K] (phi : K → EuclideanSpace ℂ I)
    (hphi : ∀ k, IsState (phi k)) (T : ℕ) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) :
    let Pi := samplePi (pureSamples phi)
    let lam := minPositiveEigenvalue (meanSampleDensity phi)
    0 < lam ∧ lam ≤ 1 ∧
    (effectProb Pi rho - (1 - lam) ^ T ≤ (projectionBranch phi T false rho).trace.re ∧
      (projectionBranch phi T false rho).trace.re ≤ effectProb Pi rho) ∧
    (Pi * rho = rho * Pi → 1 - (1 - lam) ^ T ≤ rootFidelity (projectionChannel phi T rho) rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
