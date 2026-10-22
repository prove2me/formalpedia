-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_quantum_deficit_and_allocation
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.quantum_deficit_and_allocation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:39:26.763762+00:00
-- url     : https://prove2.me/theorems/dab3d3a9-ac93-4a16-850e-8ae66deb0aa0
-- title:
--   Quantum-rate deficit and feasible allocation
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. Let $1/2\le\eta<1$, $N_S\ge0$, and $(1-\eta)N_S\ge2$. Then
--
--   $$g_n(\eta N_S)-g_n((1-\eta)N_S)\ge\ln\eta-\ln(1-\eta)-\frac1{\eta(1-\eta)N_S}.$$
--
--   For any $\epsilon>0$, set $\lambda=[\eta(1-\eta)\epsilon N_S\ln2]^{-1}$. If $\lambda\in[0,1]$ and $\lambda(1-\eta)N_S\ge2$, the displayed quantum coding rate $q_\lambda=g_b(\eta\lambda N_S)-g_b((1-\eta)\lambda N_S)$ obeys
--
--   $$\left|\frac{\ln\eta-\ln(1-\eta)}{\ln2}-q_\lambda\right|\le\epsilon.$$
--
--   The benchmark is the limiting quantum rate, and the allocation preserves its required feasibility conditions.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 7, Proposition 5: quantum rate deficit and allocation rule

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.7,9, Proposition 5: both the nats bound and the feasible photon
allocation giving an epsilon-bit deficit from the LIMITING quantum benchmark.
This does not identify a finite-budget operational capacity with that limit. -/
theorem quantum_deficit_and_allocation (eta budget : ℝ)
    (heta : 1 - eta ≤ eta) (heta1 : eta < 1)
    (hbudget : 0 ≤ budget) (hthreshold : 2 ≤ (1 - eta) * budget) :
    (Real.log eta - Real.log (1 - eta) - 1 / (eta * (1 - eta) * budget) ≤
      g (eta * budget) - g ((1 - eta) * budget)) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      let share := 1 / (eta * (1 - eta) * epsilon * budget * Real.log 2)
      share ∈ Set.Icc (0 : ℝ) 1 → 2 ≤ share * (1 - eta) * budget →
      |(Real.log eta - Real.log (1 - eta)) / Real.log 2 -
        (thermalEntropy (eta * share * budget) -
          thermalEntropy ((1 - eta) * share * budget))| ≤ epsilon) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
