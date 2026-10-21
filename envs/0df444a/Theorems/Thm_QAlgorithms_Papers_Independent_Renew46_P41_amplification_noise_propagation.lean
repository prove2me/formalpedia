-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P41_amplification_noise_propagation
-- name    : QAlgorithms.Papers.Independent.Renew46.P41.amplification_noise_propagation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:23:15.114062+00:00
-- url     : https://prove2.me/theorems/1121a2cd-b6e9-4e20-8608-9c5542816c6a
-- title:
--   Propagation of amplifier noise to clone noise and Gaussian fidelity
-- statement:
--   Let $N,M$ be positive integers with $N\le M$, let $\alpha\in\mathbb C$ be unknown, and use $[x_j,p_k]=i\delta_{jk}$ and $a_j=(x_j+ip_j)/\sqrt2$. Thus a vacuum quadrature has variance $1/2$. All implementations below are chosen independently of $\alpha$, and the conclusions hold for every $\alpha$.
--
--   In the Fourier-concentration, gain-$G=M/N$ amplification, and Fourier-distribution architecture, replace the vacuum idler by an independent zero-mean isotropic Gaussian idler of quadrature variance $v\ge1/2$. Originals are coherent and all blanks are vacuum. Let $s=(G-1)v$ denote the ADDED amplifier quadrature noise and $s_{\min}=(G-1)/2$. A unitary realizing the architecture can be chosen before $\alpha$ and $v$. Each clone has the same displaced thermal reduced density, with variance $V$ and added noise $\delta=V-1/2$ satisfying
--
--   $$V=\frac{G/2+s+(M-1)/2}{M},\qquad \delta=\frac1N-\frac1M+\frac{s-s_{\min}}M,\qquad F=\frac1{1+\delta}.$$
--
--   In particular, $\delta\ge1/N-1/M$, with equality if and only if $s=s_{\min}$. For $s_{\min}\le s<t$, clone variance increases strictly and the corresponding Gaussian coherent-state fidelity decreases strictly. The input Gaussian density and all output reduced densities are realized on full Fock space.
--
--   This states the propagation and attainment equivalence for the displayed architecture. It does not identify the bare idler variance $v$ with the added noise $s$, and does not infer fidelity from moments for non-Gaussian states.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, PDF p. 3, Eqs.(9)–(12) and adjacent text

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3, Eqs.(9)--(12): added amplification noise propagates to each
clone with factor 1/M. Equality with the cloning noise benchmark is equivalent
to quantum-limited amplification in THIS architecture. A Gaussian idler is explicit;
moments alone are never used to infer a non-Gaussian state's fidelity. -/
theorem amplification_noise_propagation (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (W : FockWeylSystem (M + 1)) (Wone : FockWeylSystem 1) :
    ∃ U : ModeUnitary (M + 1),
      FockCanonicalAction W U (dftClonerMatrix N M hN hNM) ∧
      (∀ a : ℂ, NormalizedCoherent (fun _ : Fin 1 => a) ∧
        ∀ v : ℝ, 1 / 2 ≤ v →
        let s := addedAmplifierNoise N M v
        let delta := cloneVariance N M s - 1 / 2
        ∃ X : ModeOperator (M + 1),
          PhysicalGaussian W X (inputMean N M a) (inputCovariance M v) ∧
          IsModeDensity (unitaryConjugation U X) ∧
          (∀ l : Fin M, IsReducedDensity (unitaryConjugation U X)
            (firstModes M M (by omega) l) (displacedThermal Wone a delta)) ∧
          PhysicalGaussian Wone (displacedThermal Wone a delta) (coherentMean a)
            ((cloneVariance N M s) • 1) ∧
          (inner ℂ (coherentProduct (fun _ : Fin 1 => a))
            ((displacedThermal Wone a delta) (coherentProduct (fun _ : Fin 1 => a)))).re = 1 / (1 + delta) ∧
          cloneNoise N M ≤ delta ∧
          (delta = cloneNoise N M ↔ s = (((M : ℝ) / N - 1) / 2))) ∧
      (∀ s : ℝ, cloneVariance N M s - 1 / 2 =
        cloneNoise N M + (s - (((M : ℝ) / N - 1) / 2)) / M) ∧
      (∀ s t : ℝ, (((M : ℝ) / N - 1) / 2) ≤ s → s < t →
        cloneVariance N M s < cloneVariance N M t ∧
        1 / (cloneVariance N M t + 1 / 2) <
          1 / (cloneVariance N M s + 1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P41

end
