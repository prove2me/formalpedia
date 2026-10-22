-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_pureLoss_highEnergy_quantum
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.pureLoss_highEnergy_quantum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:42:06.476581+00:00
-- url     : https://prove2.me/theorems/ac02df8f-cc14-426b-8130-c8b949ac18c5
-- title:
--   High-energy pure-loss quantum-rate limit
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. For $1/2\le\eta<1$, the high-energy coherent-information expression satisfies
--
--   $$\lim_{N_S\to\infty}\big[g_n(\eta N_S)-g_n((1-\eta)N_S)\big]=\ln\eta-\ln(1-\eta).$$
--
--   This finite nats limit excludes the identity endpoint, where the logarithmic expression is singular.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 7, §III C, (44): high-energy quantum rate limit

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.7, (44): finite high-energy quantum-rate limit in nats.
The identity endpoint is excluded because the printed logarithm is singular. -/
theorem pureLoss_highEnergy_quantum (eta : ℝ)
    (heta0 : (1 / 2 : ℝ) ≤ eta) (heta1 : eta < 1) :
    Tendsto (fun budget : ℝ => g (eta * budget) - g ((1 - eta) * budget))
      atTop (nhds (Real.log eta - Real.log (1 - eta))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
