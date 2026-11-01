-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_detection_snr_enhancement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.detection_snr_enhancement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:47:49.968656+00:00
-- url     : https://prove2.me/theorems/46391c5b-0298-4bc4-8ed8-1b5af34385d9
-- title:
--   Detection: a factor of d = 2^e in effective SNR
-- statement:
--   Work in the retained vacuum/single-photon model, on a signal space with vacuum $|\mathrm{vac}\rangle$ and $d\ge1$ orthogonal single-photon modes. Let $b\ge0$ be the background probability per mode, with $db\le1$, and let $0\le\eta\le1$ be the reflection probability. Set
--   $$
--   \rho_0=(1-db)|\mathrm{vac}\rangle\langle\mathrm{vac}|+b\sum_{k=1}^d|k\rangle\langle k|.
--   $$
--
--   Let $|\psi\rangle$ be any unit single-photon vector with zero vacuum amplitude, let $P_\psi=|\psi\rangle\langle\psi|$, and put $\rho_1=(1-\eta)\rho_0+\eta P_\psi$.
--
--   Use the resource $|\Phi_d\rangle=d^{-1/2}\sum_{k=1}^d|k\rangle_S|k\rangle_A$, transmitting only the signal and retaining the ancillary photon perfectly. Write $P_\Phi=|\Phi_d\rangle\langle\Phi_d|$, $\sigma_0=\rho_0\otimes I_A/d$, and $\sigma_1=(1-\eta)\sigma_0+\eta P_\Phi$.
--
--   For this statement assume $0<b$, $db<1$, and $0<\eta<1$.
--   With ideal matched-state tests, the background acceptance probabilities and effective SNRs obey
--   $$
--   \Pr_{\rho_0}(P_\psi)=b,\qquad
--   \Pr_{\sigma_0}(P_\Phi)=\frac bd,\qquad
--   \frac{\eta}{\Pr_{\sigma_0}(P_\Phi)}
--   =d\,\frac{\eta}{\Pr_{\rho_0}(P_\psi)}.
--   $$
--   The resource has $e=S(\operatorname{Tr}_S P_\Phi)=\log_2 d$ bits of entanglement, where $S$ is von Neumann entropy in bits. Hence
--   $$
--   d=2^e.
--   $$
--   This identifies the detection advantage of this particular resource and measurement. The separate imaging claim remains deferred.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 1, Unnumbered main detection result; abstract and (9),(14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1,7--9, (9),(14): detection SNR enhancement is d=2^e for the
specified resource. Imaging is separately deferred. The p.7 phrase
"reduce the effective signal to noise" is read as enhance SNR, as p.8 states. -/
theorem detection_snr_enhancement (p : ModelParameters) (hb : 0 < p.b)
    (hdb : (p.d : ℝ) * p.b < 1) (heta0 : 0 < p.eta) (heta1 : p.eta < 1)
    (psi : EuclideanSpace ℂ (Fin p.d)) (hpsi : IsState psi) :
    effectProb (signalTest psi) (background p.d p.b) = p.b ∧
    effectProb (pairTest p.d) (pairAbsent p.d p.b) = p.b / (p.d : ℝ) ∧
    p.eta / effectProb (pairTest p.d) (pairAbsent p.d p.b) =
      (p.d : ℝ) * (p.eta / effectProb (signalTest psi) (background p.d p.b)) ∧
    vnEntropy (traceLeft (pairTest p.d)) = ebits p.d ∧
    (p.d : ℝ) = (2 : ℝ) ^ ebits p.d := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
