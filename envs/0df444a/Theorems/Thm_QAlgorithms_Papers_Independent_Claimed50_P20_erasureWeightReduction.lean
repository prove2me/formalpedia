-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_erasureWeightReduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.erasureWeightReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:29:06.500427+00:00
-- url     : https://prove2.me/theorems/0aea8ab3-6d47-4d77-9b67-ff8053e552df
-- title:
--   Lemma 6: erasure weight reduction and classical branch
-- statement:
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   For the qubit erasure probability $\epsilon\in[0,1]$, define
--
--   $$a=(1-\epsilon)+\lambda(1-2\epsilon)-\mu\epsilon,\qquad F(p)=(1+\mu)(1-\epsilon)+aH_2(p).$$
--
--   If $a<0$, the maximum of $F$ on $[0,1/2]$ is attained at zero and $D_{\lambda,\mu}(\mathcal N_\epsilon)=(1+\mu)(1-\epsilon)$. If $a\ge0$, its maximum is attained at $1/2$. If $a=0$, every $p\in[0,1/2]$ is optimal. Finally, for the unit resource cone $U$,
--
--   $$\{(C,Q,E): C+2Q\le1-\epsilon,\ Q+E\le0,\ C+Q+E\le1-\epsilon\}=(1-\epsilon,0,0)+U.$$
--
--   Thus only $a\ge0$ needs further nonclassical boundary optimization; the other branch is the classical endpoint's translated cone. That branch is not asserted to be the entire capacity region for all weights.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 21, Lemma 6: erasure weight reduction and classical branch

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

/-- Lemma 6, PDF p.21: full sign split. The strict-negative branch chooses p=0
and gives the translated classical cone; at zero coefficient EVERY p ties.
No claim identifies a weight-selected classical branch with the full capacity region. -/
theorem erasureWeightReduction
    (epsilon lambda mu : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    (erasureCoefficient epsilon lambda mu < 0 →
      dynamic (qubitErasure epsilon) lambda mu = (1 + mu) * (1 - epsilon) ∧
      IsGreatest (erasureScore epsilon lambda mu '' Set.Icc 0 (1 / 2))
        (erasureScore epsilon lambda mu 0)) ∧
    (0 ≤ erasureCoefficient epsilon lambda mu →
      IsGreatest (erasureScore epsilon lambda mu '' Set.Icc 0 (1 / 2))
        (erasureScore epsilon lambda mu (1 / 2))) ∧
    (erasureCoefficient epsilon lambda mu = 0 →
      ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2),
        IsGreatest (erasureScore epsilon lambda mu '' Set.Icc 0 (1 / 2))
          (erasureScore epsilon lambda mu p)) ∧
    classicalBranchRegion epsilon = {r | ∃ u ∈ unitCone, r = ![1 - epsilon, 0, 0] + u} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
