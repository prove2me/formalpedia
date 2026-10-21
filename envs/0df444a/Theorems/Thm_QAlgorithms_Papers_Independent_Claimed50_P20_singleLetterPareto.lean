-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_singleLetterPareto
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.singleLetterPareto
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:17:38.846995+00:00
-- url     : https://prove2.me/theorems/0bc3fc6e-9aeb-4e0c-8c16-542f0fc31ea8
-- title:
--   Theorem 2: single-letter optimization of the Pareto trade-off surface
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   Write $r=(C,Q,E)\in\mathbb R^3$ for signed net classical, quantum and entanglement rates, with generation positive. The one-shot region $\mathcal C^{(1)}(\mathcal N)$ is the union over such pure ensembles of the simultaneous inequalities $C+2Q\le J_\sigma$, $Q+E\le K_\sigma$, and $C+Q+E\le L_\sigma$. The independent operational region $\mathcal C(\mathcal N)$ is the Euclidean closure of achievable net rates of the catalytic protocols of Section 3: local CPTP encoder and decoder, IID noisy uses, forward noiseless classical and quantum communication, consumed Bell entanglement, and generated classical correlation, entanglement transmission and Bell entanglement. Reliability is the full trace norm of the joint $M\widehat M RB_1S_AS_B$ output minus the product of its uniform classical-correlation target and its two Bell targets. Six finite nonnegative gross rates are fixed before the error and rounding tolerances; every sufficiently large positive blocklength has an appropriate code. Classical wires are dephased; no feedback is supplied.
--
--   For $S\subseteq\mathbb R^3$, let $\operatorname{Par}(S)$ consist of its componentwise maximal points: $r\in S$ and $s\in S$, $s_i\ge r_i$ for all coordinates, imply $s=r$. Suppose for every $\lambda,\mu\ge0$ the per-use tensor-power dynamic functional converges to its single-use value. Then
--
--   $$\operatorname{Par}(\mathcal C(\mathcal N))=\operatorname{Par}(\mathcal C^{(1)}(\mathcal N)).$$
--
--   This makes the Pareto trade-off surface accessible through the single-use ensemble optimization. It asserts neither an efficient numerical algorithm nor an identification with the entire topological boundary. Normals on the boundary of the nonnegative constraint cone are included.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 12, Theorem 2: single-letter optimization of the Pareto trade-off surface

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

/-- Theorem 2, PDF pp.12--13: equality of componentwise maximal-point surfaces.
The one-use optimization has arbitrary finite reference and alphabet. No algorithmic
complexity, smoothness, or identification with the whole boundary is asserted. -/
theorem singleLetterPareto
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (hsingle : SingleLetterDynamic N) :
    pareto (operationalDynamicRegion N) = pareto (oneShotRegion N) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
