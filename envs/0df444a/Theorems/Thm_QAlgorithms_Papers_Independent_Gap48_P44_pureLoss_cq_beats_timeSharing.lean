-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_pureLoss_cq_beats_timeSharing
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.pureLoss_cq_beats_timeSharing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:40:48.963442+00:00
-- url     : https://prove2.me/theorems/fed45307-e0f0-4b13-bb05-06532bb7e19c
-- title:
--   Pure-loss CQ coding properly improves endpoint time sharing
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. For $1/2<\eta<1$, fix $N_S=50/(1-\eta)$. Let $C_0=g_b(\eta N_S)$ and $Q_1=g_b(\eta N_S)-g_b((1-\eta)N_S)$. Let $T_{CQ}$ consist of all nonnegative pairs $(C,Q)$ satisfying $C\le(1-t)C_0$, $Q\le tQ_1$ for some $t\in[0,1]$. Let $A_{CQ}$ be the union over $\lambda\in[0,1]$ of the nonnegative pairs satisfying $Q\le g_b(\eta\lambda N_S)-g_b((1-\eta)\lambda N_S)$ and $C+Q\le g_b(\eta N_S)-g_b((1-\eta)\lambda N_S)$. Then
--
--   $$T_{CQ}\subsetneq A_{CQ}.$$
--
--   This compares the figure’s two displayed endpoint codes at the same budget, with generated rates discardable. Proper inclusion permits shared endpoints.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 6, §III B / Figure 2(a): CQ trade-off versus time sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.6,8, Figure 2(a): proper improvement over the displayed same-budget
HSW/coherent-information endpoint codes, allowing common endpoints. -/
theorem pureLoss_cq_beats_timeSharing (eta : ℝ)
    (heta0 : (1 / 2 : ℝ) < eta) (heta1 : eta < 1) :
    let budget := 50 / (1 - eta)
    cqTimeSharing (thermalEntropy (eta * budget))
      (thermalEntropy (eta * budget) - thermalEntropy ((1 - eta) * budget)) ⊂
        lossCQ eta budget := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
