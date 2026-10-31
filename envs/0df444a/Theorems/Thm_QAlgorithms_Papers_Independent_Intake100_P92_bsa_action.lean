-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_bsa_action
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.bsa_action
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:29:56.178662+00:00
-- url     : https://prove2.me/theorems/3eeb1d68-ad3e-4887-9466-9b7904470d6c
-- title:
--   Full-Fock beam-splitting attack preserves Bob’s optical statistics
-- statement:
--   Work in the source's ideal asymptotic, balanced-bit model, with coherent pulse amplitude $\alpha\in\mathbb C$, mean photon number $\mu=|\alpha|^2$, channel intensity transmission $t\in[0,1]$, and trusted detector efficiency $\eta\in[0,1]$. There are no dark counts or detector dead times. Rates are per emitted time slot, including empty slots, with ideal error correction and the source's negligible unused/decoy fractions and omitted monitoring/interferometer prefactors. Write $h$ for binary entropy in bits and $P_\psi=|\psi\rangle\langle\psi|$.
--
--   For each $t$ there is one full-Fock linear isometry, fixed before the input amplitudes, implementing the source's vacuum-port beam matrix. For every finite coherent pulse train, mode by mode,
--
--   $$U_t(|\alpha_k\rangle|0\rangle)=|\sqrt t\alpha_k\rangle_B|\sqrt{1-t}\alpha_k\rangle_E.$$
--
--   The coherent coefficients are square summable and normalized, and both reduced states are the corresponding coherent projectors. For either COW time-bin coding or a DPS interference time, the wrong detector has probability zero and the correct event has probability $1-e^{-\mu t\eta}$. If $\mu>0$ and $t\eta>0$, the monitored equal-phase DPS interference has positive detection probability and visibility one. The identical equal-phase monitoring statistic applies to COW nonempty neighbors.
--
--   This identifies the actual loss-simulating optical attack and its undisturbed coding statistics.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 3, III, unnumbered: full coherent beam-splitting attack and no disturbance

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

/-- PDF p.3, Section III: full-Fock vacuum BSA and its undisturbed coding statistics.
The same fixed linear isometry acts on every pulse; arbitrary finite trains are
covered by quantifying over every amplitude at every pulse. Conditional visibility
is asserted only at a positive click rate. -/
theorem bsa_action (t eta : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (heta : eta ∈ Set.Icc (0:ℝ) 1) :
    (∃ U : Fock ≃ₗᵢ[ℂ] Fock,
      (∀ psi, U psi = passiveApply (Optics.splitter t) psi) ∧
      ∀ (n : ℕ) (alpha : Fin n → ℂ) (k : Fin n),
        U (coherentPair (alpha k) 0) =
          coherentPair ((Real.sqrt t : ℂ)*alpha k) (eveAmplitude (alpha k) t)) ∧
    (∀ alpha : ℂ, Memℓp (coherentPairCoefficients alpha 0) 2 ∧
      ‖coherentPair alpha 0‖ = 1 ∧
      (∀ mn, coherentPair alpha 0 mn = coherentCoefficient alpha mn.1 * coherentCoefficient 0 mn.2) ∧
      (∀ i j, fockReducedFirst (passiveApply (Optics.splitter t) (coherentPair alpha 0)) i j =
        coherentCoefficient ((Real.sqrt t : ℂ)*alpha) i *
          star (coherentCoefficient ((Real.sqrt t : ℂ)*alpha) j)) ∧
      (∀ i j, reducedSecond (passiveApply (Optics.splitter t) (coherentPair alpha 0)) i j =
        coherentCoefficient (eveAmplitude alpha t) i * star (coherentCoefficient (eveAmplitude alpha t) j))) ∧
    (∀ (alpha : ℂ) (a : Bool),
      Optics.thresholdEventProbability eta (!a) (cowBob alpha t a) = 0 ∧
      Optics.thresholdEventProbability eta a (cowBob alpha t a) = click (Complex.normSq alpha) t eta) ∧
    (∀ (alpha : ℂ) (s a : Bool),
      Optics.thresholdEventProbability eta (!a) (dpsBob alpha t s a) = 0 ∧
      Optics.thresholdEventProbability eta a (dpsBob alpha t s a) = click (Complex.normSq alpha) t eta) ∧
    (∀ alpha : ℂ, 0 < Complex.normSq alpha → 0 < t*eta →
      0 < Optics.thresholdEventProbability eta false (dpsBob alpha t false false) ∧
      Optics.visibility eta (dpsBob alpha t false false) = 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
