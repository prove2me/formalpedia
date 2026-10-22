-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_singlePhotonModel
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.singlePhotonModel
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:42:20.015662+00:00
-- url     : https://prove2.me/theorems/abe379ff-5a4b-451a-a4c7-a2e0473e9260
-- title:
--   IV.B.4: ideal single-photon rate estimate, Eq.(35)
-- statement:
--   In the ideal single-photon model of IV.B.4, let $\widetilde\nu_S>0$ be the sifted source clock, $t,t_B,\eta\in[0,1]$ the line, apparatus and detector transmissions, and $Q\in[0,1]$ the error. Assume negligible dark counts, honest model detection rate $R=\widetilde\nu_Stt_B\eta$, information cost $h(Q)$ and perfect error-correction leakage $h(Q)$, where $h$ is binary entropy in bits. The assigned signed rate and its physical nonnegative part obey
--
--   $$K_{\rm model}=\widetilde\nu_Stt_B\eta[1-2h(Q)],\qquad K_{\rm model}^{+}=\widetilde\nu_Stt_B\eta\max\{1-2h(Q),0\}.$$
--
--   This is the identity of the explicitly idealized rate model underlying the source's approximate equation, without a quantitative approximation assertion for an arbitrary device.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 29, IV.B.4: ideal single-photon rate estimate, Eq.(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(35), PDF p.29: ideal single-photon model identity, with honest detection
rate, negligible dark counts, information cost h(Q) and optimal EC. -/
theorem singlePhotonModel (nu t tB eta Q : ℝ) (hnu : 0 < nu)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htB : tB ∈ Set.Icc (0 : ℝ) 1)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hQ : Q ∈ Set.Icc (0 : ℝ) 1) :
    signedRate (nu*t*tB*eta) (QAlgorithms.binEntropy2 Q) (QAlgorithms.binEntropy2 Q) =
      nu*t*tB*eta*(1-2*QAlgorithms.binEntropy2 Q) ∧
    max (signedRate (nu*t*tB*eta) (QAlgorithms.binEntropy2 Q) (QAlgorithms.binEntropy2 Q)) 0 =
      nu*t*tB*eta*max (1-2*QAlgorithms.binEntropy2 Q) 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
