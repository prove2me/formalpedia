-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P08_partially_assisted_capacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P08.partially_assisted_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:18:34.107486+00:00
-- url     : https://prove2.me/theorems/aa7cddd8-0cac-454b-97b6-2a2b02e74e82
-- title:
--   Theorem 6: exact partially entanglement-assisted classical capacity
-- statement:
--   Let $\mathcal N:A\to B\otimes C$ be a finite-dimensional Hadamard broadcast channel from Section 2. Let $\mathcal C_{\rm pea}(\mathcal N)$ be the Euclidean closure of operationally achievable nonnegative classical rate pairs with entanglement assistance shared only between Alice and Bob. Such codes use arbitrary finite normalized possibly mixed shared states independent of the two independent uniform messages, message-dependent CPTP encoders on Alice's share, a local Bob POVM on his retained share and $B^n$, and a local Charlie POVM on $C^n$. There is no assistance budget, receiver communication, or Charlie assistance. Achievability requires average joint success at least $1-\epsilon$ and rates $\log_2 M_j/n\ge R_j-\delta$ for every $0<\epsilon<1$, $\delta>0$ and all sufficiently large positive $n$. Then
--
--   $$
--   \mathcal C_{\rm pea}(\mathcal N)=\{(R_B,R_C)\in\mathbb R_{\ge0}^2:\ \exists W,R,p_W,\{\varphi_{RA}^w\},\ R_B\le I(R;B\mid W)_\theta,\ R_C\le I(W;C)_\theta\}.
--   $$
--
--   Here $W,R$ have arbitrary positive finite dimensions, $p_W$ is a probability distribution, every conditional $\varphi_{RA}^w$ is pure, and $\theta_{WRBC}=\sum_w p_W(w)\lvert w\rangle\langle w\rvert\otimes(\operatorname{id}_R\otimes\mathcal N)(\varphi_{RA}^w)$. Both bounds use the same ensemble, in bits. Bob's quantity is conditional mutual information without a factor one half. The single-letter existential region has no added closure or regularization.
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, PDF p. 13, Theorem 6, §5.3: partially entanglement-assisted classical capacity of a Hadamard broadcast channel

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF p.13, Theorem 6, (101)–(103): exact Bob-only assisted classical capacity.
Assistance may be mixed with arbitrary finite dimension; the single-letter witnesses
are pure and the Bob bound is conditional mutual information, without a factor half. -/
theorem partially_assisted_capacity {a b c : ℕ} (H : HadamardData a b c) :
    pairCapacity .partiallyAssisted (hadamardChannel H) =
      {rates | partiallyAssistedRegion (hadamardChannel H) rates 0} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P08

end
