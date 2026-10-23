-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P15_additive_gap_bound
-- name    : QAlgorithms.Papers.Independent.Gap20.P15.additive_gap_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:24:26.373761+00:00
-- url     : https://prove2.me/theorems/7c9f89c6-a9a6-4edd-ad4a-01bc608d0163
-- title:
--   Remark 44: additive gap bound
-- statement:
--   Write $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ for thermal entropy in bits, with $g(0)=0$.
--
--   Let $0<\bar n<1$ and $N_S\ge0$ be finite. Define $U_1=g(N_S/(1+\bar n))-g(\bar nN_S/(1+\bar n))$ and $d=\sqrt{(1+\bar n)^2+4\bar nN_S}$. The thermal-input comparator obtained from the thermal-channel limit is $L=g(N_S+\bar n)-g((d+\bar n-1)/2)-g((d-\bar n-1)/2)$. Then
--
--   $$L\le U_1\le L+\frac1{\ln2}.$$
--
--   This is the scalar claim in Remark 44. The comparator comes from the analytic limit of (6.1), without postulating an operational capacity formula.
-- source:
--   Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels, arXiv:1708.07257v3, PDF p. 48, Remark 44

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P15

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Hamiltonian)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassChannelPower)

open scoped ENNReal

/-- Remark 44, PDF p.48: scalar gap to the analytic thermal-input lower-bound
limit. No operational definition is replaced by this scalar function. -/
theorem additive_gap_bound (noise energy : ℝ)
    (hnoise : 0 < noise) (hnoise1 : noise < 1) (henergy : 0 ≤ energy) :
    additiveCoherent noise energy ≤ additiveDataProcessing noise energy ∧
    additiveDataProcessing noise energy ≤
      additiveCoherent noise energy + 1 / Real.log 2 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P15

end
