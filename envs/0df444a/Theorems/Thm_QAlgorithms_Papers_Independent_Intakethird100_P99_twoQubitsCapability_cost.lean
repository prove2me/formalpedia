-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_twoQubitsCapability_cost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.twoQubitsCapability_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:15:54.467761+00:00
-- url     : https://prove2.me/theorems/220561c4-3909-4748-abba-68f0d31964ac
-- title:
--   Exchanging arbitrary qubits characterizes the SWAP class
-- statement:
--   For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. Transmission means one use of the gate with normalized pure product inputs, without ancillas or prior shared entanglement. Encoding and decoding axes are free local choices fixed before the unknown input. Classical messages are encoded in orthogonal states and decoded with certainty; qubit transmission preserves every superposition with the same encoding and recovery. In simultaneous tasks, a receiver may choose its local decoder according to its own sent classical bit. Simultaneous exchange of arbitrary unknown qubits is equivalent to membership in the SWAP local-equivalence class, where SWAP exchanges the two tensor factors. Precisely,
--
--   $$U\text{ exchanges two arbitrary qubits}\quad\Longleftrightarrow\quad U\sim_{\rm LU}\mathrm{SWAP}\quad\Longleftrightarrow\quad\beta_1=\beta_2=|\beta_3|=\pi/4.$$
--
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. For a transmission task $T$, write $C_H(T)=\inf\{C_H(V):V\text{ performs }T\}$. An asserted optimal gate both performs the task and has an ideal simulation at the displayed time, and every capable gate has at least its cost. For $\alpha_1>0$, SWAP attains $C_H(\mathrm{qubit}_{A\leftrightarrow B})=3\pi/[4(\alpha_1+\alpha_2+|\alpha_3|)]$. The characterization concerns free local axes, not literal equality of unprocessed matrices.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 12, IV.B.4: exchanging arbitrary qubits

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.12, IV.B.4: only the SWAP local-equivalence class exchanges arbitrary qubits;
its two signed chamber endpoints and the minimum task interaction cost are retained. -/
theorem twoQubitsCapability_cost (U H : TwoMatrix) (b a : Triple)
    (hU : HasContent U b) (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    (CanTwoQubits U ↔ TwoQubitLocalEquivalent U swapGate) ∧
    (CanTwoQubits U ↔ b 0 = Real.pi / 4 ∧ b 1 = Real.pi / 4 ∧ |b 2| = Real.pi / 4) ∧
    OptimalTask H CanTwoQubits swapGate
      (3 * Real.pi / (4 * (a 0 + a 1 + |a 2|))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
