-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_dephasingBinaryEnsemble
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.dephasingBinaryEnsemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:24:13.570584+00:00
-- url     : https://prove2.me/theorems/537d70a9-6d30-44ee-97af-d35156c5e5a8
-- title:
--   §9, unnumbered: binary ensemble suffices for dephasing boundary optimization
-- statement:
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   For $p\in[0,1]$, let $\Delta_p$ be complete dephasing with probability $p$, and let $\lambda,\mu\ge0$. Define the normalized purifications
--
--   $$|\psi_0(\nu)\rangle=\sqrt\nu|00\rangle+\sqrt{1-\nu}|11\rangle,\qquad |\psi_1(\nu)\rangle=\sqrt{1-\nu}|00\rangle+\sqrt\nu|11\rangle.$$
--
--   There exists $\nu\in[0,1/2]$ such that the equiprobable ensemble of these two states attains the dynamic maximum:
--
--   $$D_{\lambda,\mu}(\Delta_p)=J_{\sigma_\nu}+\lambda K_{\sigma_\nu}+\mu L_{\sigma_\nu}.$$
--
--   The statement also asserts that this score is a greatest feasible dynamic value. This is sufficiency for each scalarized boundary optimization; it does not claim simultaneous componentwise domination of each arbitrary ensemble.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 16, §9, unnumbered: binary ensemble suffices for dephasing boundary optimization

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

/-- Section 9, PDF pp.16--18 (29)--(31): every scalarized dynamic maximum is attained
by the displayed binary ensemble, represented by canonical reference purifications. -/
theorem dephasingBinaryEnsemble
    (p lambda mu : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 / 2 ∧
      dephasingBinaryScore p lambda mu nu = dynamic (qubitDephasing (1 - p)) lambda mu ∧
      IsGreatest (dynamicValues (qubitDephasing (1 - p)) lambda mu)
        (dephasingBinaryScore p lambda mu nu) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
