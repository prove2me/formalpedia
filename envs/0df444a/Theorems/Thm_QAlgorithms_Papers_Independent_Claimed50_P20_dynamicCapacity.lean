-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_dynamicCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.dynamicCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:13:44.167297+00:00
-- url     : https://prove2.me/theorems/989b6edd-3b0c-4047-b02b-72bc61d5d8ae
-- title:
--   Theorem 1 (Dynamic Capacity); seed paper result advertised on p.1
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   Write $r=(C,Q,E)\in\mathbb R^3$ for signed net classical, quantum and entanglement rates, with generation positive. The one-shot region $\mathcal C^{(1)}(\mathcal N)$ is the union over such pure ensembles of the simultaneous inequalities $C+2Q\le J_\sigma$, $Q+E\le K_\sigma$, and $C+Q+E\le L_\sigma$. The independent operational region $\mathcal C(\mathcal N)$ is the Euclidean closure of achievable net rates of the catalytic protocols of Section 3: local CPTP encoder and decoder, IID noisy uses, forward noiseless classical and quantum communication, consumed Bell entanglement, and generated classical correlation, entanglement transmission and Bell entanglement. Reliability is the full trace norm of the joint $M\widehat M RB_1S_AS_B$ output minus the product of its uniform classical-correlation target and its two Bell targets. Six finite nonnegative gross rates are fixed before the error and rounding tolerances; every sufficiently large positive blocklength has an appropriate code. Classical wires are dephased; no feedback is supplied.
--
--   The dynamic capacity theorem asserts
--
--   $$\mathcal C(\mathcal N)=\overline{\bigcup_{k\ge1}\frac1k\mathcal C^{(1)}(\mathcal N^{\otimes k})}.$$
--
--   The closure encloses the entire union. Block ensembles may be entangled across all channel uses. This identifies the operational region with the regularized entropic region in all signed octants.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 6, Theorem 1 (Dynamic Capacity); seed paper result advertised on p.1

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

/-- Theorem 1 (Dynamic Capacity), PDF p.6 (8)--(12), with Definitions 1--2 on p.6.
The LHS is the independent six-resource operational region, not an entropic abbreviation. -/
theorem dynamicCapacity
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    operationalDynamicRegion N = regularizedRegion N := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
