-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_noiselessCoherentSigns
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.noiselessCoherentSigns
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:40:59.15565+00:00
-- url     : https://prove2.me/theorems/d801541f-d8b5-409a-af06-42199bfa6db8
-- title:
--   V.A: noiseless coherent-information signs and limits
-- statement:
--   Set $N_c=0$ and fix finite $N\ge0$. Let $J_N(k)$ be the actual thermal-input coherent information. For $N>0$ and $k\ge0$, it is negative when $k^2<1/2$, zero at $k^2=1/2$, and positive when $k^2>1/2$. For $N=0$ it is identically zero. Moreover,
--
--   $$\lim_{k\downarrow0}J_N(k)=-g(N),\qquad J_N(1)=g(N),\qquad\lim_{k\to\infty}J_N(k)=0.$$
--
--   The boundary zero is shown explicitly in Figure 4; the word “quickly” supplies no quantified convergence rate. This describes the noiseless thermal value, not noisy-channel or all-input optimization.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 10, V.A: noiseless coherent-information signs and limits

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- V.A, p.10 and Figs.3--4, pp.13--14. SOURCE CORRECTION: "negative
otherwise" excludes the zero at k^2=1/2 marked in Fig.4; N=0 is identically
zero. "Quickly" supplies no numerical convergence rate. -/
theorem noiselessCoherentSigns (N : ℝ) (hN : 0 ≤ N) :
    (∀ k : ℝ, 0 ≤ k →
      (thermalCoherentInformation N k 0 < 0 ↔ 0 < N ∧ k ^ 2 < 1 / 2) ∧
      (thermalCoherentInformation N k 0 = 0 ↔ N = 0 ∨ k ^ 2 = 1 / 2) ∧
      (0 < thermalCoherentInformation N k 0 ↔ 0 < N ∧ 1 / 2 < k ^ 2)) ∧
    Tendsto (fun k : ℝ => thermalCoherentInformation N k 0) (𝓝[≥] 0)
      (𝓝 (-bosonicEntropy N)) ∧
    thermalCoherentInformation N 1 0 = bosonicEntropy N ∧
    Tendsto (fun k : ℝ => thermalCoherentInformation N k 0) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
