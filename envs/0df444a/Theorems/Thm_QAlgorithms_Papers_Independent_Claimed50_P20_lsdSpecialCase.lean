-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_lsdSpecialCase
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.lsdSpecialCase
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:19:48.644755+00:00
-- url     : https://prove2.me/theorems/a701a1a3-97ef-4e63-8954-5a2c813f9944
-- title:
--   Corollary 2: LSD formula special case
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   The conditional and single-input coherent-information maxima are attained and equal:
--
--   $$\max_\sigma I(A\rangle BX)_\sigma=\max_{\phi^{AA'}\ \mathrm{pure}} I(A\rangle B)_{(\mathrm{id}_A\otimes\mathcal N)(\phi)}.$$
--
--   The reference dimension on the right is arbitrary and finite. This is the exact maximum equality used by the source to describe the large-$\lambda$ LSD special case. It does not identify the one-shot coherent maximum with the unassisted quantum capacity of every channel.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 14, Corollary 2: LSD formula special case

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

/-- Corollary 2, PDF p.14: equality of attained conditional and single-state coherent maxima.
This is the displayed equality, not a raw infinite-lambda limit or an unregularized coding theorem. -/
theorem lsdSpecialCase
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    ∃ v : ℝ, IsGreatest (cqCoherentValues N) v ∧ IsGreatest (singleCoherentValues N) v := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
