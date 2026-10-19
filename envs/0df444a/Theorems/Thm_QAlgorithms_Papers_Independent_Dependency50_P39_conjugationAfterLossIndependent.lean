-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_conjugationAfterLossIndependent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.conjugationAfterLossIndependent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:42:03.397993+00:00
-- url     : https://prove2.me/theorems/7e563ddf-c14d-4352-acd4-fe28e03f4103
-- title:
--   §IX.IV: conjugation after loss
-- statement:
--   Let $\kappa_2>0$ and $0\le\kappa_1<1$. The explicit bounded operators
--
--   $$\{T_m(\kappa_2)B_n(\kappa_1):(m,n)\in\mathbb N^2\}$$
--
--   are a complete linearly independent countable Kraus family for conjugation after attenuation on the full oscillator space. Their normalization is strong and their action has a trace-norm sum on every trace-class input. The zero-loss parameter is included; the identity-loss endpoint is excluded. Linear independence is algebraic, across all finite combinations of the product indices.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 32, §IX.IV: conjugation after loss

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.32 §IX.IV: conjugation after loss has independent product Kraus
operators, including the loss parameter zero and excluding the identity endpoint. 
Printed: Section IX.IV permits 0<=kappa1<=1 and kappa2>0, then calls {T_m(kappa2) B_n(kappa1)} independent.
Changed: Require 0<=kappa1<1 and kappa2>0, retaining zero loss.
Why: At kappa1=1 every n>0 product is zero. At kappa1=0 the products are nonzero weighted matrix units. Only the identity loss endpoint must be removed.
-/
theorem conjugationAfterLossIndependent (k1 k2 : ℝ) (h1 : 0 ≤ k1)
    (h1u : k1 < 1) (h2 : 0 < k2) :
    AttenuatorRealized k1 ∧
    KrausWellDefined (productKraus (phaseKraus k2) (attenuatorKraus k1)) ∧
    LinearIndependent ℂ (productKraus (phaseKraus k2) (attenuatorKraus k1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
