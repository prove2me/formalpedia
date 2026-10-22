-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P34_operational_strong_converse
-- name    : QAlgorithms.Papers.Independent.Gap48.P34.operational_strong_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:44:16.62658+00:00
-- url     : https://prove2.me/theorems/c31433f9-033e-457c-9f2b-0f7caf08d6b7
-- title:
--   Operational strong converse above the optical classical-capacity threshold
-- statement:
--   Let $\mathcal P$ be a centered phase-insensitive bosonic Gaussian CPTP channel on the full oscillator, with $\tau\ge0$ and $\nu\ge|\tau-1|$, characterized on all states by $\chi_{\rm out}(z)=\chi_{\rm in}(\sqrt\tau z)e^{-\nu|z|^2/2}$. Set $N_B'=(\tau+\nu-1)/2$, $N_S'=\tau N_S+N_B'$ for finite $N_S\ge0$, and let $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$, continuously at zero.
--
--   For each positive integer $n$, choose any unassisted classical code with $M_n\ge1$ uniform messages, arbitrary normalized n-mode trace-class codewords (including entangled states), and a normalized collective output POVM. Write $R_n=\log_2 M_n/n$ and $p_n$ for its average decoding success. Suppose a nonnegative decreasing sequence $\delta_1(n)\to0$ satisfies $M_n^{-1}\sum_m\operatorname{Tr}(\Pi_{\lceil nN_S\rceil}\rho_m)\ge1-\delta_1(n)$, where $\Pi_L$ is the total-photon-number cutoff projector. For any fixed $R>g(N_S')-g(N_B')$, if eventually $R_n\ge R$, then
--
--   $$\lim_{n\to\infty}p_n=0.$$
--
--   This is the operational strong converse at the known capacity threshold; it does not impose a decay speed on the allowed input tail.
-- source:
--   Strong converse for the classical capacity of optical quantum communication channels, arXiv:1401.4161v3, PDF p. 2, Introduction and Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P34

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Renew46.P30
  (HilbertDensity nuclearExpansionTrace mixedLikelihood
   TraceClassCPTP multiKet multiDisplacement)

open QAlgorithms.Papers.Independent.Claimed50.P30 (ModeOperator)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P08 (codeRate)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.2 and Corollary 1, p.12: success tends to zero above the
capacity threshold g(NSprime)-g(NBprime). This states the operational converse,
not a new achievability theorem. The abstract's unconditional exponential-speed
claim is false under (32) and is separately recorded in HARD.md. -/
theorem operational_strong_converse (P : OpticalChannel) (NS : ℝ) (hNS : 0 ≤ NS) :
    StrongConverseAt P NS
      (thermalEntropy (outputEnergy P NS) - thermalEntropy (noiseEnergy P)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P34

end
