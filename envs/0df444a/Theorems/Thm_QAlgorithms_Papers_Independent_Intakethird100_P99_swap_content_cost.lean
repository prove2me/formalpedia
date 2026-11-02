-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_swap_content_cost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.swap_content_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:11:01.10982+00:00
-- url     : https://prove2.me/theorems/7b45926d-f52f-42da-8a99-f35814bbb3a9
-- title:
--   SWAP interaction content, branch choice, and cost
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. Assume $\alpha_1>0$. For $\mathrm{SWAP}:|i,j\rangle\mapsto|j,i\rangle$, both $\frac{\pi}{4}(1,1,1)$ and $\frac{\pi}{4}(1,1,-1)$ describe its physical local-equivalence class, and
--
--   $$C_H(\mathrm{SWAP})=\frac{3\pi}{4(\alpha_1+\alpha_2+|\alpha_3|)}.$$
--
--   The positive branch attains this cost when $\alpha_3\ge0$, and the negative branch when $\alpha_3\le0$; both tie at zero. A branch cost is the infimum of nonnegative times satisfying that branch of s-majorization.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 7, III.D.3: SWAP content and interaction cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.7, III.D.3: SWAP's two signed contents and cost; the positive branch is
optimal for positive a3, the negative branch for negative a3, and both tie at zero. -/
theorem swap_content_cost (H : TwoMatrix) (a : Triple)
    (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    HasContent swapGate ![Real.pi / 4, Real.pi / 4, Real.pi / 4] ∧
    HasContent swapGate ![Real.pi / 4, Real.pi / 4, -Real.pi / 4] ∧
    interactionCost H swapGate =
      ENNReal.ofReal (3 * Real.pi / (4 * (a 0 + a 1 + |a 2|))) ∧
    (0 ≤ a 2 → branchCost a ![Real.pi / 4, Real.pi / 4, Real.pi / 4] =
      interactionCost H swapGate) ∧
    (a 2 ≤ 0 → branchCost a ![Real.pi / 4, Real.pi / 4, -Real.pi / 4] =
      interactionCost H swapGate) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
