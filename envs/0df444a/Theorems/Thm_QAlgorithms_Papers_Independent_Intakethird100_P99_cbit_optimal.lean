-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_cbit_optimal
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.cbit_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:49:15.821936+00:00
-- url     : https://prove2.me/theorems/53b7a1b3-6ac5-4a5c-8713-4ea0b607cae9
-- title:
--   Result 4: CNOT minimizes one-cbit transmission time
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. Transmission means one use of the gate with normalized pure product inputs, without ancillas or prior shared entanglement. Encoding and decoding axes are free local choices fixed before the unknown input. Classical messages are encoded in orthogonal states and decoded with certainty; qubit transmission preserves every superposition with the same encoding and recovery. In simultaneous tasks, a receiver may choose its local decoder according to its own sent classical bit. For a transmission task $T$, write $C_H(T)=\inf\{C_H(V):V\text{ performs }T\}$. An asserted optimal gate both performs the task and has an ideal simulation at the displayed time, and every capable gate has at least its cost. Assume $\alpha_1>0$. The CNOT gate, whose first qubit controls the second, attains
--
--   $$C_H(\mathrm{cbit}_{A\to B})=C_H(\mathrm{CNOT})=\frac{\pi}{4\alpha_1}.$$
--
--   The same gate is a minimizer for transmission in the opposite direction after free changes of local axes. Every gate capable of the chosen one-cbit task costs at least this much; no uniqueness of the minimizer is asserted.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 10, Result 4: minimum interaction time for one classical bit

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.10, Result 4: CNOT attains the minimum over every gate that can send one
perfect classical bit; its being a minimizer is not a uniqueness assertion. -/
theorem cbit_optimal (H : TwoMatrix) (a : Triple)
    (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    OptimalTask H CanCbit cnot (Real.pi / (4 * a 0)) ∧
      OptimalTask H (fun U => CanCbit (reverseParties U)) cnot
        (Real.pi / (4 * a 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
