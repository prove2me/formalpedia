-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_hadamardStrongAdditivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.hadamardStrongAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:22:26.295909+00:00
-- url     : https://prove2.me/theorems/600d0da6-262c-4b78-a637-c621aead002d
-- title:
--   Lemma 2: strong additivity with a Hadamard channel
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   Let $\mathcal M:C'\to D$ be any other CPTP channel between nonzero finite registers, and assume $\mathcal N$ is Hadamard, meaning that an isometric dilation has an entanglement-breaking full complement. For all $\lambda,\mu\ge0$,
--
--   $$D_{\lambda,\mu}(\mathcal N\otimes\mathcal M)=D_{\lambda,\mu}(\mathcal N)+D_{\lambda,\mu}(\mathcal M).$$
--
--   The second channel is unrestricted, and the tensor-product functional optimizes arbitrary joint inputs. This strong additivity drives Hadamard single-letterization; the proof's degrading factorization is not an extra assumption.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 15, Lemma 2: strong additivity with a Hadamard channel

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

/-- Lemma 2, PDF pp.15--16: strong additivity with one Hadamard factor and ANY other channel. -/
theorem hadamardStrongAdditivity
    {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (N : Superop A B) (M : Superop C D) (hN : IsChannel N) (hM : IsChannel M)
    (hH : IsHadamard N) (lambda mu : ℝ) (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    dynamic (tensorChannel N M) lambda mu = dynamic N lambda mu + dynamic M lambda mu := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
