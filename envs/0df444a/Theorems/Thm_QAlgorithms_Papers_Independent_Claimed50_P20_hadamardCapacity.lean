-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_hadamardCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.hadamardCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:21:41.247866+00:00
-- url     : https://prove2.me/theorems/0862d586-033a-496a-9e07-96af0540e144
-- title:
--   Theorem 3: Hadamard dynamic capacity single-letterizes
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   Write $r=(C,Q,E)\in\mathbb R^3$ for signed net classical, quantum and entanglement rates, with generation positive. The one-shot region $\mathcal C^{(1)}(\mathcal N)$ is the union over such pure ensembles of the simultaneous inequalities $C+2Q\le J_\sigma$, $Q+E\le K_\sigma$, and $C+Q+E\le L_\sigma$. The independent operational region $\mathcal C(\mathcal N)$ is the Euclidean closure of achievable net rates of the catalytic protocols of Section 3: local CPTP encoder and decoder, IID noisy uses, forward noiseless classical and quantum communication, consumed Bell entanglement, and generated classical correlation, entanglement transmission and Bell entanglement. Reliability is the full trace norm of the joint $M\widehat M RB_1S_AS_B$ output minus the product of its uniform classical-correlation target and its two Bell targets. Six finite nonnegative gross rates are fixed before the error and rounding tolerances; every sufficiently large positive blocklength has an appropriate code. Classical wires are dephased; no feedback is supplied.
--
--   Assume $\mathcal N$ is Hadamard: an isometric dilation has a full complementary channel that is entanglement breaking under every finite reference extension. Then
--
--   $$\mathcal C(\mathcal N)=\mathcal C^{(1)}(\mathcal N).$$
--
--   The one-shot union is unclosed on the right. This removes regularization for the whole signed region; closedness is part of the conclusion's content.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 15, Theorem 3: Hadamard dynamic capacity single-letterizes

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P20

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3, PDF p.15: the operational Hadamard region equals the UNCLOSED one-shot union. -/
theorem hadamardCapacity
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (hH : IsHadamard N) :
    operationalDynamicRegion N = oneShotRegion N := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
