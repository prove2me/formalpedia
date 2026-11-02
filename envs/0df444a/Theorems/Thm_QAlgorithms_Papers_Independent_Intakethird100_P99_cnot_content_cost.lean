-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_cnot_content_cost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.cnot_content_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:08:49.563123+00:00
-- url     : https://prove2.me/theorems/dd8da2eb-0cc9-4e09-bb1d-076ee858c307
-- title:
--   CNOT interaction content and cost
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. Assume $\alpha_1>0$. The gate $\mathrm{CNOT}:|i,j\rangle\mapsto|i,i\oplus j\rangle$, with $\oplus$ denoting addition modulo two, has canonical interaction content $(\pi/4,0,0)$ up to local unitaries and global phase, and
--
--   $$C_H(\mathrm{CNOT})=\frac{\pi}{4\alpha_1}.$$
--
--   The interaction-content assertion concerns the physical local-equivalence class; the raw CNOT matrix is not an SU(4) canonical exponential.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 7, III.D.1: CNOT content and interaction cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.7, III.D.1 and p.13: CNOT content is projective local equivalence, not
literal equality of the raw CNOT matrix with an SU(4) canonical exponential. -/
theorem cnot_content_cost (H : TwoMatrix) (a : Triple)
    (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    HasContent cnot ![Real.pi / 4, 0, 0] ∧
      interactionCost H cnot = ENNReal.ofReal (Real.pi / (4 * a 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
