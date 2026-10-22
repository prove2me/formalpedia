-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_classical_deficit_and_allocation
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.classical_deficit_and_allocation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:40:08.450198+00:00
-- url     : https://prove2.me/theorems/265ca61b-6dfb-417b-96b2-d9d69ea7397b
-- title:
--   Limited-entanglement classical deficit and allocation
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. Let $0\le\eta<1$, $N_S\ge0$, $\lambda\in[0,1]$, and $\lambda(1-\eta)N_S\ge2$. Put $c_\lambda=g_n(\lambda N_S)+g_n(\eta N_S)-g_n((1-\eta)\lambda N_S)$ and $d_\lambda=c_1-c_\lambda$. Then
--
--   $$d_\lambda\le\frac5{6\lambda N_S(1-\eta)}.$$
--
--   For $\epsilon>0$, the feasible allocation $\lambda_\epsilon=5/[6\epsilon N_S(1-\eta)\ln2]$ gives $|d_{\lambda_\epsilon}|/\ln2\le\epsilon$, provided $\lambda_\epsilon\in[0,1]$ and $\lambda_\epsilon(1-\eta)N_S\ge2$.
--
--   The first display is in nats; the allocation gives an error in bits. The difference on the left is the one explicitly computed in the source proof.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 9, Proposition 6: limited-entanglement classical deficit and allocation rule

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.9-10, Proposition 6: the proof supplies the missing printed LHS.
The first bound is in nats; the allocation conclusion is in bits.
Printed: only 5/(6 lambda N_S (1-eta)); changed: attach the difference explicitly
computed at the beginning of the proof. Why: the bound otherwise has no subject.
Independent moderation of this source-domain interpretation remains pending. -/
theorem classical_deficit_and_allocation (eta share budget : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hshare : share ∈ Set.Icc (0 : ℝ) 1)
    (hbudget : 0 ≤ budget) (hthreshold : 2 ≤ share * (1 - eta) * budget) :
    (g budget + g (eta * budget) - g ((1 - eta) * budget) -
      (g (share * budget) + g (eta * budget) - g ((1 - eta) * share * budget)) ≤
        5 / (6 * share * budget * (1 - eta))) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      let allocation := 5 / (6 * epsilon * budget * (1 - eta) * Real.log 2)
      allocation ∈ Set.Icc (0 : ℝ) 1 → 2 ≤ allocation * (1 - eta) * budget →
      |thermalEntropy budget + thermalEntropy (eta * budget) -
        thermalEntropy ((1 - eta) * budget) -
        (thermalEntropy (allocation * budget) + thermalEntropy (eta * budget) -
          thermalEntropy ((1 - eta) * allocation * budget))| ≤ epsilon) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
