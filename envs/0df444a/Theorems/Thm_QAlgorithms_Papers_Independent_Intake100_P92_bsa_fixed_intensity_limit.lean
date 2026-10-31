-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_bsa_fixed_intensity_limit
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.bsa_fixed_intensity_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:32:18.058322+00:00
-- url     : https://prove2.me/theorems/d7e5ea3a-63ff-4ac4-a0d1-2198065cf0a9
-- title:
--   Fixed-intensity long-distance coefficients of the exact BSA rates
-- statement:
--   Work in the source's ideal asymptotic, balanced-bit model, with coherent pulse amplitude $\alpha\in\mathbb C$, mean photon number $\mu=|\alpha|^2$, channel intensity transmission $t\in[0,1]$, and trusted detector efficiency $\eta\in[0,1]$. There are no dark counts or detector dead times. Rates are per emitted time slot, including empty slots, with ideal error correction and the source's negligible unused/decoy fractions and omitted monitoring/interferometer prefactors. Write $h$ for binary entropy in bits and $P_\psi=|\psi\rangle\langle\psi|$.
--
--   Fix $\mu>0$ and $0<\eta\le1$; intensity is held fixed while $t\downarrow0$. For the exact BSA rates computed from the constructed conditional ensembles,
--
--   $$\lim_{t\downarrow0}\frac{r_{\rm COW}}{t\eta}=\frac\mu2\left[1-h\!\left(\frac{1-e^{-\mu}}2\right)\right],$$
--   $$\lim_{t\downarrow0}\frac{r_{\rm DPS}}{t\eta}=\mu\left[1-2h\!\left(\frac{1-e^{-2\mu}}2\right)+h\!\left(\frac{1-e^{-4\mu}}2\right)\right].$$
--
--   These identify the first-order coefficients at fixed intensity. They assert neither a limit of optimizers nor a certified numerical optimum.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 4, III, unnumbered: fixed-intensity BSA long-distance coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- PDF p.4: fixed-intensity long-distance coefficients. No interchange of
optimization and limit, no distance threshold, and no rounded optimizer is claimed. -/
theorem bsa_fixed_intensity_limit (alpha : ℂ) (eta : ℝ)
    (hmu : 0 < Complex.normSq alpha) (heta : 0 < eta ∧ eta ≤ 1) :
    Tendsto (fun t => cowRate alpha t eta / (t*eta)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Complex.normSq alpha / 2 *
        (1-QAlgorithms.binEntropy2 ((1-Real.exp (-Complex.normSq alpha))/2)))) ∧
    Tendsto (fun t => dpsRate alpha t eta / (t*eta)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Complex.normSq alpha *
        (1-2*QAlgorithms.binEntropy2 ((1-Real.exp (-2*Complex.normSq alpha))/2) +
          QAlgorithms.binEntropy2 ((1-Real.exp (-4*Complex.normSq alpha))/2)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
