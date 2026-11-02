-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_twoCbits_optimal
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.twoCbits_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:50:00.171512+00:00
-- url     : https://prove2.me/theorems/57c8ce6e-a897-4de6-8ec9-520efa7fdd11
-- title:
--   Result 5: optimal simultaneous bidirectional cbits
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. Transmission means one use of the gate with normalized pure product inputs, without ancillas or prior shared entanglement. Encoding and decoding axes are free local choices fixed before the unknown input. Classical messages are encoded in orthogonal states and decoded with certainty; qubit transmission preserves every superposition with the same encoding and recovery. In simultaneous tasks, a receiver may choose its local decoder according to its own sent classical bit. For a transmission task $T$, write $C_H(T)=\inf\{C_H(V):V\text{ performs }T\}$. An asserted optimal gate both performs the task and has an ideal simulation at the displayed time, and every capable gate has at least its cost. Assume $\alpha_1>0$. A gate with interaction content $\beta_*=\frac{\pi}{4}(1,1,2\alpha_3/(\alpha_1+\alpha_2))$ attains the simultaneous bidirectional-cbit cost
--
--   $$C_H(\mathrm{cbit}_{A\leftrightarrow B})=\frac{\pi}{2(\alpha_1+\alpha_2)}.$$
--
--   The displayed content lies in the gate chamber. The bound applies to every capable gate and scales inversely with the strength of $H$.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 11, Result 5: time-optimal bidirectional classical transmission

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.11, Result 5: an attaining content and the minimum over all simultaneous
bidirectional classical-bit gates. Arbitrary nonzero Hamiltonian strength is allowed. -/
theorem twoCbits_optimal (H : TwoMatrix) (a : Triple)
    (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    HasContent (contentGate (optimalTransmissionContent a)) (optimalTransmissionContent a) ∧
      OptimalTask H CanTwoCbits (contentGate (optimalTransmissionContent a))
        (Real.pi / (2 * (a 0 + a 1))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
