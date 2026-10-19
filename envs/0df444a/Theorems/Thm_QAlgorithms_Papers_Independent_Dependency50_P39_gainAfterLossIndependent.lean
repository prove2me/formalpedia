-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_gainAfterLossIndependent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.gainAfterLossIndependent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:40:09.540988+00:00
-- url     : https://prove2.me/theorems/0850f686-0f19-4f74-8870-e04e8e8867d8
-- title:
--   §IX.I: gain after loss
-- statement:
--   Let $0\le\kappa_1<1<\kappa_2$. The explicit products on the full Fock space form a complete linearly independent countable Kraus family:
--
--   $$\{A_m(\kappa_2)B_n(\kappa_1):(m,n)\in\mathbb N^2\}.$$
--
--   The amplifier acts after the attenuator. Completeness is strong operator completeness, and the Kraus sum converges in trace norm for every trace-class input. The loss endpoint $\kappa_1=0$ is retained: these products are nonzero scalar multiples of matrix units. Identity endpoints, which introduce zero indexed operators, are excluded.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 30, §IX.I: gain after loss

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.30 §IX.I: gain after loss has an independent product Kraus family.
The loss parameter zero is retained: the products are weighted matrix units. 
Printed: Section IX.I permits kappa2>=1 and kappa1<=1, then calls the full family {A_m(kappa2) B_n(kappa1)} independent.
Changed: Require 0<=kappa1<1<kappa2, retaining kappa1=0.
Why: At kappa1=1 all B_n with n>0 vanish; at kappa2=1 all A_m with m>0 vanish. These zero members preclude independence of the unreduced indexed family. At kappa1=0 the products are nonzero weighted matrix units, so excluding that endpoint would be unnecessary.
-/
theorem gainAfterLossIndependent (k1 k2 : ℝ) (h1 : 0 ≤ k1) (h1u : k1 < 1)
    (h2 : 1 < k2) :
    AttenuatorRealized k1 ∧ AmplifierRealized k2 ∧
    KrausWellDefined (productKraus (amplifierKraus k2) (attenuatorKraus k1)) ∧
    LinearIndependent ℂ (productKraus (amplifierKraus k2) (attenuatorKraus k1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
