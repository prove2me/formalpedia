-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_hswSpecialCase
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.hswSpecialCase
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:20:44.675895+00:00
-- url     : https://prove2.me/theorems/088e711b-dd25-440d-b6a0-9a3f09840ede
-- title:
--   Corollary 3: HSW formula special case
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   The following maxima are attained and equal:
--
--   $$\max_\sigma\bigl[I(A\rangle BX)_\sigma+I(X;B)_\sigma\bigr]=\max_{\{p_x,\psi_x^{A'}\ \mathrm{pure}\}} I(X;B).$$
--
--   On the right, the normalized pure states are unentangled channel inputs and their outputs carry their classical ensemble label. The left side optimizes the sum on a single common ensemble. This is the source's precise HSW formula special case, without replacing the one-shot maximum by regularized classical capacity.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 14, Corollary 3: HSW formula special case

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

/-- Corollary 3, PDF pp.14--15: the common-ensemble SUM has the same attained maximum
as the Holevo information of unentangled pure channel inputs. -/
theorem hswSpecialCase
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    ∃ v : ℝ, IsGreatest (cqSumValues N) v ∧ IsGreatest (pureHolevoValues N) v := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
