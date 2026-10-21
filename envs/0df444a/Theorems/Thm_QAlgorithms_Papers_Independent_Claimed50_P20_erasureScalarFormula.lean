-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_erasureScalarFormula
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.erasureScalarFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:28:21.050489+00:00
-- url     : https://prove2.me/theorems/e1d33e54-5adc-45c0-9be5-6fd33b58c9e0
-- title:
--   Lemma 5: scalar form of the erasure dynamic functional
-- statement:
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   For the qubit erasure channel $\mathcal N_\epsilon$ with $\epsilon\in[0,1]$, put
--
--   $$F(p)=(1-\epsilon)(1+H_2(p))+\lambda(1-2\epsilon)H_2(p)+\mu[(1-\epsilon)-\epsilon H_2(p)].$$
--
--   Then the scalar maximum is attained and
--
--   $$D_{\lambda,\mu}(\mathcal N_\epsilon)=\max_{p\in[0,1/2]}F(p).$$
--
--   Moreover its one-shot region consists exactly of the signed triples satisfying, for one common $p\in[0,1/2]$, $C+2Q\le(1-\epsilon)(1+H_2(p))$, $Q+E\le(1-2\epsilon)H_2(p)$ and $C+Q+E\le1-\epsilon-\epsilon H_2(p)$. This is a scalar simplification of the common-ensemble functional; it keeps both signs of the entropy coefficient.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 20, Lemma 5: scalar form of the erasure dynamic functional

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

/-- Lemma 5, PDF pp.20--21 (34): attained scalar maximum and one-letter region.
The negative entropy-coefficient branch is retained; the proof's highest-entropy
choice is valid only for a nonnegative coefficient (as clarified by Lemma 6). -/
theorem erasureScalarFormula
    (epsilon lambda mu : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    (∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 / 2 ∧
      dynamic (qubitErasure epsilon) lambda mu = erasureScore epsilon lambda mu p ∧
      IsGreatest (erasureScore epsilon lambda mu '' Set.Icc 0 (1 / 2))
        (erasureScore epsilon lambda mu p)) ∧
    oneShotRegion (qubitErasure epsilon) =
      {r | ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 / 2 ∧ rateConstraints (erasureBounds epsilon p) r} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
