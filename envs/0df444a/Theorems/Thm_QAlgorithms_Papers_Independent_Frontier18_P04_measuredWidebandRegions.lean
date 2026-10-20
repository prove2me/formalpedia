-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P04_measuredWidebandRegions
-- name    : QAlgorithms.Papers.Independent.Frontier18.P04.measuredWidebandRegions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:51:17.645982+00:00
-- url     : https://prove2.me/theorems/58622f59-145e-4609-8656-ef5da2b5aed4
-- title:
--   Wideband measured capacity and homodyne water filling
-- statement:
--   Let $m\ge1$, $\hbar>0$, $\eta_i\ge0$, $\sum_i\eta_i=1$, and $P_i\ge0$ be finite transmitted power budgets. Independent senders use coherent states in independent modes of frequency $\omega_j=2\pi j/T$, $j\ge1$, with frequency-independent transmissivities and no fixed bandwidth cutoff. The transmitted power constraint is $\sum_j\hbar\omega_j\mathbb E|\alpha_{ij}|^2/T\le P_i$. Define the closed operational regions by vanishing average decoding error as duration $T$ tends to infinity, allowing growing frequency support. Rates are nats per unit time. Then
--
--   $$
--   \mathcal C_{\rm hom}^{\rm wb}=\mathcal C_{\rm het}^{\rm wb}
--   =\left\{R\ge0:\ \sum_{i\in S}R_i\le\sqrt{\frac{\sum_{i\in S}\eta_iP_i}{\pi\hbar}}\ \text{for every }S\subseteq\{1,\ldots,m\}\right\}.
--   $$
--
--   For a received power $q\ge0$, the homodyne received photon spectrum is
--
--   $$
--   f_q(\omega)=\begin{cases}\displaystyle\frac{\sqrt{\pi q/\hbar}}{\omega}-\frac14,&0<\omega\le4\sqrt{\pi q/\hbar},\\0,&\text{otherwise}.\end{cases}
--   $$
--
--   For any $q_A,q_B\ge0$, put $f=f_{q_A}$, $F=f_{q_A+q_B}$ and $b=F-f$. These spectra are nonnegative at positive frequencies, and their power and information integrands are integrable. Writing $\mathcal P(h)=\int_0^\infty\hbar\omega h(\omega)\,d\omega/(2\pi)$ and $\mathcal I(h)=\int_0^\infty\log(1+4h(\omega))\,d\omega/(4\pi)$, one has
--
--   $$
--   \mathcal P(f)=q_A,\qquad\mathcal P(b)=q_B,\qquad
--   \mathcal I(f)=\sqrt{\frac{q_A}{\pi\hbar}},\qquad
--   \mathcal I(F)=\sqrt{\frac{q_A+q_B}{\pi\hbar}}.
--   $$
--
--   For $0<\eta<1$, these allocations, divided by the respective transmissivities, achieve the lower-right corner $(\mathcal I(f),\mathcal I(F)-\mathcal I(f))$ with transmitted powers $(q_A/\eta,q_B/(1-\eta))$. Exchanging the users gives the other corner and the individual Bob spectrum. The capacity equality itself includes endpoint transmissivities. This supplies both the measured wideband region and the homodyne allocation that attains its corners.
--
--   **Formalization Note** The printed second coordinate in (20) subtracts Bob's individual bound; it is corrected to subtract Alice's bound, as required by saturation of (16a),(16c). The homodyne spectrum is not asserted to be a heterodyne optimizer. Independent moderation of the correction is pending.
-- source:
--   Multiple-Access Bosonic Communications, arXiv:quant-ph/0506171v2, PDF p. 3, §II.C, (16)–(22): wideband measured regions and water filling

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P04

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology NNReal

namespace QAlgorithms.Papers.Independent.Frontier18.P04

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- arXiv:quant-ph/0506171v2, PDF pp.3–4,(16)–(22): equal measured wideband
regions, with homodyne water filling and a corner-achieving allocation.
Printed (20) subtracts Bob's bound in the second coordinate; the corrected lower-right
corner subtracts Alice's bound, as required by (16a),(16c). The spectra below are
received spectra: divide by the sender's transmissivity only in the interior case.
Their swapped version gives (18) and the upper-left corner. The rate-region equality
also includes endpoint transmissivities without division. -/
theorem measuredWidebandRegions :
    (∀ (m : ℕ), 1 ≤ m → ∀ (hbar : ℝ), 0 < hbar →
      ∀ eta power : Fin m → ℝ,
      (∀ i, 0 ≤ eta i) → (∑ i, eta i = 1) → (∀ i, 0 ≤ power i) →
      widebandCapacity 1 (1 / 4) hbar eta power =
        {R | (∀ i, 0 ≤ R i) ∧ ∀ S : Finset (Fin m),
          (∑ i ∈ S, R i) ≤ Real.sqrt ((∑ i ∈ S, eta i * power i) / (Real.pi * hbar))} ∧
      widebandCapacity 2 (1 / 2) hbar eta power =
        widebandCapacity 1 (1 / 4) hbar eta power) ∧
    (∀ hbar qA qB : ℝ, 0 < hbar → 0 ≤ qA → 0 ≤ qB →
      let f := homodyneSpectrum hbar qA
      let total := homodyneSpectrum hbar (qA + qB)
      let b := fun omega => total omega - f omega
      (∀ omega, 0 < omega → 0 ≤ f omega ∧ 0 ≤ b omega) ∧
      IntegrableOn (fun omega => hbar * omega * f omega / (2 * Real.pi)) (Set.Ioi 0) ∧
      IntegrableOn (fun omega => hbar * omega * b omega / (2 * Real.pi)) (Set.Ioi 0) ∧
      IntegrableOn (fun omega => Real.log (1 + 4 * f omega) / (4 * Real.pi)) (Set.Ioi 0) ∧
      IntegrableOn (fun omega => Real.log (1 + 4 * total omega) / (4 * Real.pi)) (Set.Ioi 0) ∧
      spectrumPower hbar f = qA ∧ spectrumPower hbar b = qB ∧
      homodyneSpectrumRate f = Real.sqrt (qA / (Real.pi * hbar)) ∧
      homodyneSpectrumRate total = Real.sqrt ((qA + qB) / (Real.pi * hbar)) ∧
      (∀ eta : ℝ, 0 < eta → eta < 1 →
        (![Real.sqrt (qA / (Real.pi * hbar)),
          Real.sqrt ((qA + qB) / (Real.pi * hbar)) - Real.sqrt (qA / (Real.pi * hbar))] : Fin 2 → ℝ)
          ∈ widebandCapacity 1 (1 / 4) hbar (![eta, 1 - eta] : Fin 2 → ℝ)
            (![qA / eta, qB / (1 - eta)] : Fin 2 → ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P04

end
