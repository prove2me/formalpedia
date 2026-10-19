-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_lossAfterGainIndependent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.lossAfterGainIndependent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:40:54.455987+00:00
-- url     : https://prove2.me/theorems/aeb437d6-07fa-4c35-ad77-b2e08f200174
-- title:
--   §IX.II: loss after gain
-- statement:
--   Let $\kappa_1>1$ and $0<\kappa_2<1$. On the full Fock space, loss after gain has the complete linearly independent countable Kraus family
--
--   $$\{B_m(\kappa_2)A_n(\kappa_1):(m,n)\in\mathbb N^2\}.$$
--
--   The operators are the explicit bounded shifts of Eqs. (4.6) and (5.5). Normalization converges strongly and the map converges in trace norm on every trace-class input. The strict loss bounds exclude the vacuum-replacer and identity degeneracies.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 31, §IX.II: loss after gain

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.31 §IX.II: loss after gain has an independent product Kraus family.
The vacuum-replacer and identity loss endpoints are excluded. 
Printed: Section IX.II permits kappa2<=1 and kappa1>=1, then calls {B_m(kappa2) A_n(kappa1)} independent.
Changed: Require 0<kappa2<1<kappa1.
Why: The identity endpoints give zero positive-index Kraus operators. At kappa2=0, B_m(0) A_n(kappa1)=0 whenever n>m. Excluding exactly these endpoints removes the explicit zero members.
-/
theorem lossAfterGainIndependent (k1 k2 : ℝ) (h1 : 1 < k1)
    (h2 : 0 < k2) (h2u : k2 < 1) :
    AmplifierRealized k1 ∧ AttenuatorRealized k2 ∧
    KrausWellDefined (productKraus (attenuatorKraus k2) (amplifierKraus k1)) ∧
    LinearIndependent ℂ (productKraus (attenuatorKraus k2) (amplifierKraus k1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
