-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_entanglementAssistedSpecialCase
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.entanglementAssistedSpecialCase
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:18:59.465413+00:00
-- url     : https://prove2.me/theorems/ab25131e-c80e-4469-b08f-1730e3548a39
-- title:
--   Corollary 1: entanglement-assisted formula special case
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   At zero dynamic weights, the two attained single-letter maxima agree:
--
--   $$\max_\sigma I(AX;B)_\sigma=\max_{\phi^{AA'}\ \mathrm{pure}} I(A;B)_{(\mathrm{id}_A\otimes\mathcal N)(\phi)}.$$
--
--   The right side optimizes all normalized pure bipartite inputs with arbitrary finite reference. The Lean statement asserts a common greatest value of both feasible value sets, preserving attainment. This is the entanglement-assisted formula special case; no operational coding theorem is assumed.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 14, Corollary 1: entanglement-assisted formula special case

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

/-- Corollary 1, PDF p.14: equality of the attained single-letter maxima at lambda=mu=0. -/
theorem entanglementAssistedSpecialCase
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    ∃ v : ℝ, IsGreatest (cqMutualValues N) v ∧ IsGreatest (singleMutualValues N) v := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
