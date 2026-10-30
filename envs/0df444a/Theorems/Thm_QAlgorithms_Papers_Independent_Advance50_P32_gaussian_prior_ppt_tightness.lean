-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_gaussian_prior_ppt_tightness
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.gaussian_prior_ppt_tightness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:26:07.627114+00:00
-- url     : https://prove2.me/theorems/ddc5d2fc-32f6-4bbe-ba00-88e5d37a566c
-- title:
--   Section 5.2, unnumbered Gaussian-prior equality claim
-- statement:
--   Fix $s>0$ and $\alpha>0$, take identity noise ($\lambda=1$), and choose the normalized displacement density $q_\alpha(\xi)=(\alpha/\pi)e^{-\alpha\|\xi\|^2}$ with uniform common phase rotation. For $E=\mathbb E[\rho_{\xi,\theta}\otimes\rho_{\xi,\theta}]$, the paper asserts that its PPT bound is tight:
--
--   $$\bar F=\sup_{\substack{\Omega\ge0,\ \Omega^\Gamma\ge0\\\operatorname{Tr}_B\Omega=I_A}}\operatorname{Tr}(E\Omega).$$
--
--   Here $\bar F$ is the optimum over all entanglement-breaking channels, and the supremum ranges over bounded operators on the full two-mode space. This records the asserted equality for the paper's fixed-squeezing setup, without adding an $s=1$ restriction or assuming Gaussian optimality as a premise.
--
--   **Formalization Note** The printed $\alpha\ge0$ is restricted by the standing probability-density assumption: $q_0$ is identically zero and is not a flat probability law. The paper attributes Gaussian optimality to [9]; its applicability beyond the coherent case should receive independent moderation.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 11, Section 5.2, Gaussian-prior paragraph after Eq. (26)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology TensorProduct

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State IsTraceClassChannel BreaksTraceClassEntanglement
   productCoeff traceSize rotationMeasure)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel vacuum realFockTracePair)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section 5.2, p.11: the paper's asserted Gaussian-prior tightness, for fixed s>0
and identity noise (lambda=1). Its alpha>=0 is restricted by the standing
probability-density assumption to alpha>0. No extra Gaussian-optimality premise
is inserted. The cited Gaussian optimality [9] warrants independent scrutiny. -/
theorem gaussian_prior_ppt_tightness (s alpha : ℝ) (hs : 0 < s) (halpha : 0 < alpha) :
    averageBenchmark s (gaussianPrior alpha) (fun X => X) =
      pptOptimum (ensembleOperator s (gaussianPrior alpha) (fun X => X)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
