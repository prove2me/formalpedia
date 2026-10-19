-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_attenuatorSemigroup
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorSemigroup
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:33:25.736624+00:00
-- url     : https://prove2.me/theorems/f0da381d-9987-4cd9-b3a7-ba7be2402613
-- title:
--   Eq.(4.26): attenuator semigroup
-- statement:
--   Let $0<\kappa_1,\kappa_2<1$, and let $C_{1,\kappa}$ denote the channel given by the complete bounded family $B_\ell(\kappa)$ of Eq. (4.6). On every trace-class input,
--
--   $$C_{1,\kappa_1}\circ C_{1,\kappa_2}=C_{1,\kappa_1\kappa_2}.$$
--
--   The doubly indexed products $B_m(\kappa_1)B_n(\kappa_2)$ and the single family $B_\ell(\kappa_1\kappa_2)$ have strongly complete normalizations, and their trace-norm sums agree on every trace-class operator. The first factor acts after the second. This is an equality of the complete maps, not only their diagonal input laws.
--
--   The operators act on $H=\ell^2(\mathbb N;\mathbb C)$, with orthonormal basis $|n\rangle$ for $n\ge0$. The fixed source families are
--   $$
--   \begin{aligned}
--   B_\ell(b)&=\sum_{m\ge0}\sqrt{\binom{m+\ell}{\ell}}\,\sqrt{1-b^2}^{\,\ell}b^m|m\rangle\langle m+\ell|,\\
--   A_\ell(g)&=g^{-1}\sum_{m\ge0}\sqrt{\binom{m+\ell}{\ell}}\,\sqrt{1-g^{-2}}^{\,\ell}g^{-m}|m+\ell\rangle\langle m|,\\
--   T_\ell(t)&=(\sqrt{1+t^2})^{-1}\sum_{n=0}^{\ell}\sqrt{\binom\ell n}(\sqrt{1+t^2})^{-n}(\sqrt{1+t^{-2}})^{-(\ell-n)}|\ell-n\rangle\langle n|.
--   \end{aligned}
--   $$
--   Here $0\le b\le1$, $g\ge1$, and $t>0$. Endpoints are $B_\ell(0)=|0\rangle\langle\ell|$, $B_0(1)=A_0(1)=I$, and $B_\ell(1)=A_\ell(1)=0$ for $\ell>0$. When used, $T_\ell(0)=|0\rangle\langle\ell|$ is specified separately. Infinite operator sums that define a channel are interpreted in trace norm on trace-class inputs.
-- source:
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 17, Eq.(4.26): attenuator semigroup

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.17 Eq.(4.26): the attenuator semigroup on every trace-class input. -/
theorem attenuatorSemigroup (k1 k2 : ℝ) (h1 : 0 < k1) (h1u : k1 < 1)
    (h2 : 0 < k2) (h2u : k2 < 1) :
    AttenuatorRealized k1 ∧ AttenuatorRealized k2 ∧ AttenuatorRealized (k1 * k2) ∧
      KrausEquivalent (productKraus (attenuatorKraus k1) (attenuatorKraus k2))
        (attenuatorKraus (k1 * k2)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
