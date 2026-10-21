-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P08_classical_quantum_capacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P08.classical_quantum_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:16:50.459461+00:00
-- url     : https://prove2.me/theorems/2ab57af7-5789-4bce-bf08-aaf3a1b4c791
-- title:
--   Theorem 4: exact classical–quantum capacity
-- statement:
--   Let $\mathcal N:A\to B\otimes C$ be a finite-dimensional Hadamard broadcast channel as in Section 2. Its unassisted classical–quantum capacity is the Euclidean closure of achievable nonnegative pairs $(Q_B,R_C)$. A block code uses a uniform Charlie message of positive integer size $M_C$, arbitrary density codewords $\rho_{RA^n}^m$ with $\dim R=M_B\ge1$, a local CPTP decoder $B^n\to\widehat R$, and a local POVM on $C^n$. The joint decoded state, averaged with weight $1/M_C$, must have half trace-norm distance at most $\epsilon$ from the product of a normalized maximally correlated message/copy state and the rank-$M_B$ maximally entangled $R\widehat R$ state. There is no entanglement assistance. Achievability requires these codes for every $0<\epsilon<1$, $\delta>0$ and all sufficiently large positive $n$, with the two logarithmic dimension rates at least $(Q_B-\delta,R_C-\delta)$. Then
--
--   $$
--   \mathcal C_{\rm cq}(\mathcal N)=\{(Q_B,R_C)\in\mathbb R_{\ge0}^2:\ \exists W,R,p_W,\{\varphi_{RA}^w\},\ Q_B\le I(R\rangle BW)_\theta,\ R_C\le I(W;C)_\theta\}.
--   $$
--
--   The alphabet $W$ and reference $R$ have arbitrary positive finite dimensions, $p_W$ is a probability distribution, the conditional states $\varphi_{RA}^w$ are pure, and $\theta_{WRBC}=\sum_w p_W(w)\lvert w\rangle\langle w\rvert\otimes(\operatorname{id}_R\otimes\mathcal N)(\varphi_{RA}^w)$. The coherent information is $I(R\rangle BW)_\theta=\sum_w p_W(w)[H(B)_{\theta^w}-H(RB)_{\theta^w}]$, in bits. This exact operational equality has no extra closure on the existential region.
--
--   **Formalization Note** The code average corrects the printed $1/M_B$ in (65),(75) to $1/M_C$; the two cardinalities remain independent.
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, PDF p. 10, Theorem 4, §4.3: classical–quantum capacity of a Hadamard broadcast channel

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF p.10, Theorem 4, (71)–(73): exact unassisted classical–quantum capacity.
Bob's bound is coherent information, with arbitrary finite reference dimension.
The operational joint criterion uses the normalized 1/M_C message average;
printed (65),(75) use 1/M_B, a normalization typo corrected in the code definition. -/
theorem classical_quantum_capacity {a b c : ℕ} (H : HadamardData a b c) :
    pairCapacity .classicalQuantum (hadamardChannel H) =
      {rates | classicalQuantumRegion (hadamardChannel H) rates 0} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P08

end
