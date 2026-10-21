-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P08_classical_capacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P08.classical_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:16:00.345041+00:00
-- url     : https://prove2.me/theorems/648f16e6-8c5b-48bc-b0ca-df4a7cb10586
-- title:
--   Theorem 2: exact classical capacity of a Hadamard broadcast channel
-- statement:
--   Let $\mathcal N:A\to B\otimes C$ be the finite-dimensional Hadamard broadcast channel constructed from the rank-one POVM and normalized prepared vectors in Section 2. Define its unassisted classical capacity $\mathcal C_{\rm cl}(\mathcal N)$ as the Euclidean closure of achievable nonnegative rate pairs. Achievability means that for every $0<\epsilon<1$ and $\delta>0$, all sufficiently large positive blocklengths admit independent uniform messages of positive integer sizes $M_B,M_C$, arbitrary density codewords on $A^{\otimes n}$, and separate local POVMs, with average joint success at least $1-\epsilon$ and $\log_2 M_j/n\ge R_j-\delta$. Codewords may be entangled across channel uses. There is no initial entanglement assistance or receiver communication. Then
--
--   $$
--   \mathcal C_{\rm cl}(\mathcal N)=\{(R_B,R_C)\in\mathbb R_{\ge0}^2:\ \exists W,Z,p_{WZ},\{\varphi_A^z\},\ R_B\le I(Z;B\mid W)_\theta,\ R_C\le I(W;C)_\theta\}.
--   $$
--
--   Here $W,Z$ are arbitrary nonempty finite alphabets, $p_{WZ}$ is a normalized joint distribution, every $\varphi_A^z$ is a pure density operator depending only on $z$, and $\theta_{WZBC}=\sum_{w,z}p_{WZ}(w,z)\lvert w,z\rangle\langle w,z\rvert\otimes\mathcal N(\varphi_A^z)$. Both bounds use the same ensemble; entropy is in bits. The equality gives both achievability and converse without regularization, an added sum-rate constraint, a cardinality cap or an added closure on the displayed existential region.
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, PDF p. 4, Theorem 2, §3.3: classical capacity of a Hadamard broadcast channel (seed paper result)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF p.4, Theorem 2, (19)–(21): exact unassisted classical capacity.
The left side is the closed arbitrary-block operational region; the right is
the single-letter existential pure-ensemble region, with no added closure. -/
theorem classical_capacity {a b c : ℕ} (H : HadamardData a b c) :
    pairCapacity .classical (hadamardChannel H) =
      {rates | classicalRegion (hadamardChannel H) rates 0} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P08

end
