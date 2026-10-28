-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_thermalMixture_identity
-- name    : QAlgorithms.Papers.Independent.Support50.P06.thermalMixture_identity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:33:07.596856+00:00
-- url     : https://prove2.me/theorems/ea59cd5a-cafb-4cce-adf2-388e7ff284d5
-- title:
--   Equivalent Gaussian coherent and photon-number thermal mixtures
-- statement:
--   Let $N\ge0$ be finite, let $|\alpha\rangle$ be the normalized oscillator coherent state, and let $|j\rangle$ denote the orthonormal photon-number basis. The normalized thermal density of mean $N$ has the equivalent representations
--
--   $$\rho_T(N)=\int_{\mathbb C}|\alpha\rangle\langle\alpha|\,d\mu_N(\alpha)=\sum_{j=0}^\infty\frac{N^j}{(N+1)^{j+1}}|j\rangle\langle j|,$$
--
--   where $d\mu_N(\alpha)=e^{-|\alpha|^2/N}\,d^2\alpha/(\pi N)$ for $N>0$, and $\mu_0=\delta_0$. The measure is a probability law, all coherent matrix coefficients are integrable, and its moments exist with $\int\alpha\,d\mu_N=0$ and $\int|\alpha|^2\,d\mu_N=N$.
--
--   This identifies the Gaussian signal average with the same full thermal state as the geometric mixture. The zero-variance case is the vacuum point mass, rather than the singular printed density evaluated at zero.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 4, §IV.B, (18)–(19): equivalent thermal-state representations

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (18)–(19): the same normalized thermal density is the Gaussian
coherent mixture and the geometric photon-number mixture. Integrability and
probability normalization are conclusions. N=0 uses delta_0, since the printed
Lebesgue density is singular there; the photon representation fixes this limit. -/
theorem thermalMixture_identity (N : ℝ) (hN : 0 ≤ N) :
    IsProbabilityMeasure (complexNormal N 0) ∧
    Integrable (fun alpha : ℂ => alpha) (complexNormal N 0) ∧
    (∫ alpha : ℂ, alpha ∂complexNormal N 0) = 0 ∧
    Integrable (fun alpha : ℂ => Complex.normSq alpha) (complexNormal N 0) ∧
    (∫ alpha : ℂ, Complex.normSq alpha ∂complexNormal N 0) = N ∧
    IsDensity (identicalThermalKernel 1 N) ∧
    coherentMixture N = identicalThermalKernel 1 N ∧
    (∀ a b : NumberString 1,
      Integrable (fun alpha : ℂ => productCoherentKernel 1 (fun _ => alpha) a b)
        (complexNormal N 0) ∧
      identicalThermalKernel 1 N a b = ∑' j : ℕ,
        ((N ^ j / (N + 1) ^ (j + 1) : ℝ) : ℂ) *
          (if a = (fun _ => j) ∧ b = (fun _ => j) then 1 else 0)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
