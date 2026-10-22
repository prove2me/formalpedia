-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P34_channel_specializations
-- name    : QAlgorithms.Papers.Independent.Gap48.P34.channel_specializations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:47:29.676353+00:00
-- url     : https://prove2.me/theorems/f0a838e3-e084-4a61-9355-458fec4a334f
-- title:
--   Thermal, additive-noise, and noisy-amplifier strong converse thresholds
-- statement:
--   Consider arbitrary unassisted classical code families on the full Fock space, with every positive blocklength, positive uniform message count, arbitrary normalized codewords and normalized collective POVM. Fix finite $N_S\ge0$, and impose the average-state occupation constraint at total photon cutoff $\lceil nN_S\rceil$ with a nonnegative decreasing tail tending to zero. Let $g$ denote thermal entropy in bits. The following are strong converse thresholds:
--
--   $$\begin{aligned}C_{\rm thermal}&=g(\eta N_S+(1-\eta)N_B)-g((1-\eta)N_B),&&0\le\eta\le1,\quad N_B\ge0,\\C_{\rm additive}&=g(N_S+\bar n)-g(\bar n),&&\bar n\ge0,\\C_{\rm amplifier}&=g(GN_S+(G-1)(N+1))-g((G-1)(N+1)),&&G\ge1,\quad N\ge0.\end{aligned}$$
--
--   For each respective actual Gaussian channel, success tends to zero whenever rates eventually exceed its displayed threshold by a fixed positive amount. The channels are specified on all states by their characteristic laws, equivalently by $(\tau,\nu)=(\eta,(1-\eta)(2N_B+1))$, $(1,2\bar n)$, and $(G,(G-1)(2N+1))$. The thresholds include the endpoint channels and spontaneous amplifier noise.
-- source:
--   Strong converse for the classical capacity of optical quantum communication channels, arXiv:1401.4161v3, PDF p. 13, Unnumbered conclusion after Corollary 1; (8),(15)–(17)

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

/-- PDF p.13, unnumbered conclusion, with channel laws (8), p.4,
and thresholds (15)--(17), pp.4--5. All three families are included.
The actual block channels are fixed on every state by OpticalChannel's Weyl
law. Endpoints eta=0, eta=1, zero additive noise, G=1 and NS=0 are allowed.
Amplifier noise is (G-1)*(N+1), including spontaneous emission. -/
theorem channel_specializations :
    (∀ (eta NB NS : ℝ), 0 ≤ eta → eta ≤ 1 → 0 ≤ NB → 0 ≤ NS →
      ∀ P : OpticalChannel, P.tau = eta → P.nu = (1 - eta) * (2 * NB + 1) →
        StrongConverseAt P NS
          (thermalEntropy (eta * NS + (1 - eta) * NB) - thermalEntropy ((1 - eta) * NB))) ∧
    (∀ (nbar NS : ℝ), 0 ≤ nbar → 0 ≤ NS →
      ∀ P : OpticalChannel, P.tau = 1 → P.nu = 2 * nbar →
        StrongConverseAt P NS (thermalEntropy (NS + nbar) - thermalEntropy nbar)) ∧
    (∀ (G N NS : ℝ), 1 ≤ G → 0 ≤ N → 0 ≤ NS →
      ∀ P : OpticalChannel, P.tau = G → P.nu = (G - 1) * (2 * N + 1) →
        StrongConverseAt P NS
          (thermalEntropy (G * NS + (G - 1) * (N + 1)) -
            thermalEntropy ((G - 1) * (N + 1)))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P34

end
