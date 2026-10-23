-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_pureLoss_ce_beats_timeSharing
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.pureLoss_ce_beats_timeSharing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:41:30.772348+00:00
-- url     : https://prove2.me/theorems/91e758b1-2945-4f03-8da4-544faa97f877
-- title:
--   Pure-loss CE coding properly improves endpoint time sharing
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. For $0<\eta<1$, fix $N_S=50/(1-\eta)$. Define $C_0=g_b(\eta N_S)$, $C_1=g_b(N_S)+g_b(\eta N_S)-g_b((1-\eta)N_S)$, and $E_1=g_b(N_S)$. Let $T_{CE}$ contain the nonnegative pairs $(C,E_c)$ with $C\le(1-t)C_0+tC_1$ and $E_c\ge tE_1$ for some $t\in[0,1]$. Let $A_{CE}$ contain the nonnegative pairs satisfying, for some $\lambda\in[0,1]$, $C\le g_b(\lambda N_S)+g_b(\eta N_S)-g_b((1-\eta)\lambda N_S)$ and $C\le g_b(\eta N_S)-g_b((1-\eta)\lambda N_S)+E_c$. Then
--
--   $$T_{CE}\subsetneq A_{CE}.$$
--
--   The second coordinate is consumed entanglement, the negative of the source’s net entanglement rate. The endpoints have the same photon budget.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 7, §III B / Figure 2(b): CE trade-off versus time sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.7-8, Figure 2(b): proper CE-family inclusion at the caption's budget.
The second coordinate is nonnegative entanglement CONSUMPTION. -/
theorem pureLoss_ce_beats_timeSharing (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    let budget := 50 / (1 - eta)
    ceTimeSharing (thermalEntropy (eta * budget))
      (thermalEntropy budget + thermalEntropy (eta * budget) -
        thermalEntropy ((1 - eta) * budget)) (thermalEntropy budget) ⊂
      lossCE eta budget := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
