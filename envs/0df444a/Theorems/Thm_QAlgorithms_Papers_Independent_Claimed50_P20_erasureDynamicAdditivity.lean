-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_erasureDynamicAdditivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.erasureDynamicAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:29:50.252988+00:00
-- url     : https://prove2.me/theorems/fca4173b-2e31-4e9c-924f-82b779e85ed5
-- title:
--   Lemma 7: dynamic additivity for equal erasure channels
-- statement:
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   Let $\epsilon\in[0,1]$ and let $\mathcal N_\epsilon$ be the qubit erasure channel with its orthogonal flag. For all $\lambda,\mu\ge0$,
--
--   $$D_{\lambda,\mu}(\mathcal N_\epsilon\otimes\mathcal N_\epsilon)=D_{\lambda,\mu}(\mathcal N_\epsilon)+D_{\lambda,\mu}(\mathcal N_\epsilon).$$
--
--   The block input ensemble is arbitrary and may be entangled. The same erasure probability is used in both factors, while both signs of the entropy coefficient are allowed. This is the source's equal-channel dynamic additivity statement, without an unsupported all-blocklength induction premise.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 21, Lemma 7: dynamic additivity for equal erasure channels

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

/-- Lemma 7, PDF pp.21--22: same erasure parameter, ALL nonnegative weights.
The two mu-term differences printed on p.22 should be sums; this is a proof typo,
not a hypothesis or a restriction on this additivity statement. -/
theorem erasureDynamicAdditivity
    (epsilon lambda mu : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    dynamic (tensorChannel (qubitErasure epsilon) (qubitErasure epsilon)) lambda mu =
      dynamic (qubitErasure epsilon) lambda mu + dynamic (qubitErasure epsilon) lambda mu := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
