-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_qubitCapability_cost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.qubitCapability_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:14:30.626245+00:00
-- url     : https://prove2.me/theorems/3877d1c4-f63f-419f-9746-0af51594bef0
-- title:
--   Unknown-qubit transmission criterion and optimal cost
-- statement:
--   For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. Transmission means one use of the gate with normalized pure product inputs, without ancillas or prior shared entanglement. Encoding and decoding axes are free local choices fixed before the unknown input. Classical messages are encoded in orthogonal states and decoded with certainty; qubit transmission preserves every superposition with the same encoding and recovery. In simultaneous tasks, a receiver may choose its local decoder according to its own sent classical bit. An arbitrary unknown qubit can be transmitted from $A$ to $B$ exactly when $\beta_1=\beta_2=\pi/4$, and the same criterion holds in the opposite direction. Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. For a transmission task $T$, write $C_H(T)=\inf\{C_H(V):V\text{ performs }T\}$. An asserted optimal gate both performs the task and has an ideal simulation at the displayed time, and every capable gate has at least its cost. For $\alpha_1>0$,
--
--   $$C_H(\mathrm{qubit}_{A\to B})=\frac{\pi}{2(\alpha_1+\alpha_2)},\qquad\beta_*=\frac{\pi}{4}\left(1,1,\frac{2\alpha_3}{\alpha_1+\alpha_2}\right).$$
--
--   The canonical gate with content $\beta_*$ attains the bound in either chosen direction. The same fixed recovery preserves every normalized superposition, not just the two basis states.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 11, IV.B.3: transmitting a qubit

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF pp.11–12, IV.B.3: unknown-qubit transmission has the same optimal content and
cost as Result 5; its criterion includes coherence for every superposition. -/
theorem qubitCapability_cost (U H : TwoMatrix) (b a : Triple)
    (hU : HasContent U b) (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    (CanQubit U ↔ b 0 = Real.pi / 4 ∧ b 1 = Real.pi / 4) ∧
    (CanQubit (reverseParties U) ↔ b 0 = Real.pi / 4 ∧ b 1 = Real.pi / 4) ∧
    HasContent (contentGate (optimalTransmissionContent a)) (optimalTransmissionContent a) ∧
    OptimalTask H CanQubit (contentGate (optimalTransmissionContent a))
      (Real.pi / (2 * (a 0 + a 1))) ∧
    OptimalTask H (fun V => CanQubit (reverseParties V))
      (contentGate (optimalTransmissionContent a)) (Real.pi / (2 * (a 0 + a 1))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
