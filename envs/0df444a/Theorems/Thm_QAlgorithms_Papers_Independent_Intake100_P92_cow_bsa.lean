-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cow_bsa
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cow_bsa
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:30:41.508233+00:00
-- url     : https://prove2.me/theorems/7aa87d6d-fb86-4f14-9f47-27809e898bf4
-- title:
--   COW beam-splitting conditional states, spectra, Holevo information and rate
-- statement:
--   Work in the source's ideal asymptotic, balanced-bit model, with coherent pulse amplitude $\alpha\in\mathbb C$, mean photon number $\mu=|\alpha|^2$, channel intensity transmission $t\in[0,1]$, and trusted detector efficiency $\eta\in[0,1]$. There are no dark counts or detector dead times. Rates are per emitted time slot, including empty slots, with ideal error correction and the source's negligible unused/decoy fractions and omitted monitoring/interferometer prefactors. Write $h$ for binary entropy in bits and $P_\psi=|\psi\rangle\langle\psi|$.
--
--   Let $a=\sqrt{1-t}\alpha$ and $\gamma=e^{-\mu(1-t)}$. Eve’s conditional operators are $\rho_0=P_{a,0}$ and $\rho_1=P_{0,a}$ on full two-mode Fock space. Each is pure and normalized; the modulus of the overlap is $\gamma$, and their average has eigenvalues $(1+\gamma)/2,(1-\gamma)/2$, including endpoint zeros. Direct calculation of Bob-event postselection gives zero operator for the wrong bit and $(1-e^{-\mu t\eta})\rho_a$ for the correct bit. Thus, whenever clicks occur, conditioning on Bob gives these same states, and
--
--   $$\chi_{AE}=\chi_{BE}=h\!\left(\frac{1-\gamma}{2}\right),\qquad r_{\rm COW}=\frac{1-e^{-\mu t\eta}}2\left[1-h\!\left(\frac{1-\gamma}{2}\right)\right].$$
--
--   The same expression applies to COWm1 and COWm2 with Alice’s pairing. Constructed states and the rate retain their explicit continuous extensions at zero clicks. This supplies a full-state, attack-specific information calculation.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 3, III, Eqs.(3)–(5): exact COW BSA conditional states, spectra, Holevo information and rate

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

/-- PDF p.3, (3)–(5): COW/COWm1/COWm2 BSA, including the actual postselected
operators, their spectra, entropy, and per-slot ideal signed rate. At zero clicks
these are explicit continuous extensions, not conditional probability quotients. -/
theorem cow_bsa (alpha : ℂ) (t eta : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (heta : eta ∈ Set.Icc (0:ℝ) 1) :
    (∀ a, weightedAncillaTrace (cowE alpha t a) = 1 ∧ ensembleEntropyBits (cowE alpha t a) = 0) ∧
    ‖inner ℂ (cowE alpha t false ()) (cowE alpha t true ())‖ = gammaE alpha t ∧
    HasUnitaryGramSpectrum (ancillaGram (equiprobableEnsemble (cowE alpha t false) (cowE alpha t true)))
      (fun z => if z.1 then (1-gammaE alpha t)/2 else (1+gammaE alpha t)/2) ∧
    (∀ a b, cowHerald alpha t eta a b =
      (if a = b then (click (Complex.normSq alpha) t eta : ℂ) else 0) •
        ensembleDensityCoefficients (fun i n => cowE alpha t a i n)) ∧
    binaryHolevoBits (cowE alpha t false) (cowE alpha t true) =
      QAlgorithms.binEntropy2 ((1-gammaE alpha t)/2) ∧
    cowRate alpha t eta = click (Complex.normSq alpha) t eta / 2 *
      (1-QAlgorithms.binEntropy2 ((1-gammaE alpha t)/2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
