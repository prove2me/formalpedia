-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_dps_bsa
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.dps_bsa
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:31:19.655423+00:00
-- url     : https://prove2.me/theorems/18200f1e-8fbc-4e49-b1f7-c53d0b90f993
-- title:
--   DPS beam-splitting mixtures, spectra, Holevo information and rate
-- statement:
--   Work in the source's ideal asymptotic, balanced-bit model, with coherent pulse amplitude $\alpha\in\mathbb C$, mean photon number $\mu=|\alpha|^2$, channel intensity transmission $t\in[0,1]$, and trusted detector efficiency $\eta\in[0,1]$. There are no dark counts or detector dead times. Rates are per emitted time slot, including empty slots, with ideal error correction and the source's negligible unused/decoy fractions and omitted monitoring/interferometer prefactors. Write $h$ for binary entropy in bits and $P_\psi=|\psi\rangle\langle\psi|$.
--
--   Set $a=\sqrt{1-t}\alpha$ and $\gamma=e^{-\mu(1-t)}$. Construct the actual mixtures
--
--   $$\rho_0=\tfrac12(P_{a,a}+P_{-a,-a}),\qquad \rho_1=\tfrac12(P_{a,-a}+P_{-a,a}).$$
--
--   Each conditional spectrum is $\{(1+\gamma^4)/2,(1-\gamma^4)/2\}$. Their average is the tensor square of the uniform one-pulse mixture, with spectrum $\{x^2,xy,xy,y^2\}$, where $x=(1+\gamma^2)/2$ and $y=(1-\gamma^2)/2$. The computed heralded operators are zero for a wrong bit and $(1-e^{-\mu t\eta})\rho_a$ for a correct bit. Consequently
--
--   $$\chi_{AE}=\chi_{BE}=2h\!\left(\frac{1-\gamma^2}{2}\right)-h\!\left(\frac{1-\gamma^4}{2}\right),\quad r_{\rm DPS}=(1-e^{-\mu t\eta})(1-\chi_{AE}).$$
--
--   States and rates include their continuous zero-click extension. The calculation retains the mixed conditional states and all spectrum multiplicities.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 3, III, Eqs.(6)–(7): exact DPS BSA mixtures, spectra, Holevo information and rate

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

/-- PDF pp.3–4, (6),(7): actual mixed DPS conditional states, their spectra,
Holevo information and rate. The conditional spectrum uses gamma_E^4; the
unconditional spectrum is the product spectrum with one-pulse overlap gamma_E^2. -/
theorem dps_bsa (alpha : ℂ) (t eta : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (heta : eta ∈ Set.Icc (0:ℝ) 1) :
    (∀ a, weightedAncillaTrace (dpsE alpha t a) = 1 ∧
      HasUnitaryGramSpectrum (ancillaGram (dpsE alpha t a))
        (fun s => if s then (1-(gammaE alpha t)^4)/2 else (1+(gammaE alpha t)^4)/2) ∧
      ensembleEntropyBits (dpsE alpha t a) = QAlgorithms.binEntropy2 ((1-(gammaE alpha t)^4)/2)) ∧
    (∀ i j : ℕ × ℕ,
      ((ensembleDensityCoefficients (fun k n => dpsE alpha t false k n) i j +
        ensembleDensityCoefficients (fun k n => dpsE alpha t true k n) i j)/2) =
        ((coherentCoefficient (eveAmplitude alpha t) i.1 *
          star (coherentCoefficient (eveAmplitude alpha t) j.1) +
          coherentCoefficient (-eveAmplitude alpha t) i.1 *
            star (coherentCoefficient (-eveAmplitude alpha t) j.1))/2) *
        ((coherentCoefficient (eveAmplitude alpha t) i.2 *
          star (coherentCoefficient (eveAmplitude alpha t) j.2) +
          coherentCoefficient (-eveAmplitude alpha t) i.2 *
            star (coherentCoefficient (-eveAmplitude alpha t) j.2))/2)) ∧
    HasUnitaryGramSpectrum (ancillaGram (equiprobableEnsemble (dpsE alpha t false) (dpsE alpha t true)))
      (fun z => ((1+(if z.1 then -1 else 1)*(gammaE alpha t)^2)/2) *
        ((1+(if z.2 then -1 else 1)*(gammaE alpha t)^2)/2)) ∧
    (∀ a b, dpsHerald alpha t eta a b =
      (if a = b then (click (Complex.normSq alpha) t eta : ℂ) else 0) •
        ensembleDensityCoefficients (fun i n => dpsE alpha t a i n)) ∧
    binaryHolevoBits (dpsE alpha t false) (dpsE alpha t true) =
      2*QAlgorithms.binEntropy2 ((1-(gammaE alpha t)^2)/2) -
        QAlgorithms.binEntropy2 ((1-(gammaE alpha t)^4)/2) ∧
    dpsRate alpha t eta = click (Complex.normSq alpha) t eta *
      (1-2*QAlgorithms.binEntropy2 ((1-(gammaE alpha t)^2)/2) +
        QAlgorithms.binEntropy2 ((1-(gammaE alpha t)^4)/2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
