-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_gainAfterConjugationIndependent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.gainAfterConjugationIndependent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:43:20.795996+00:00
-- url     : https://prove2.me/theorems/c43f63cd-34a7-491e-8306-4459afadd527
-- title:
--   §IX.VI: gain after conjugation
-- statement:
--   Let $\kappa_1>0$ and $\kappa_2>1$. Gain after conjugation on the full Fock space has the complete linearly independent countable Kraus family
--
--   $$\{A_m(\kappa_2)T_n(\kappa_1):(m,n)\in\mathbb N^2\}.$$
--
--   The operators are the source's explicit amplifier and phase-conjugator operators. Normalization is strong operator normalization and every trace-class input has a trace-norm output sum. The identity gain endpoint, which leaves zero operators in the full indexed family, is excluded.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 33, §IX.VI: gain after conjugation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF pp.32–33 §IX.VI: gain after conjugation has an independent product
Kraus family when the gain is strictly greater than one. 
Printed: Section IX.VI permits kappa2>=1 and kappa1>0, then calls {A_m(kappa2) T_n(kappa1)} independent.
Changed: Require kappa2>1 and kappa1>0.
Why: At kappa2=1, A_m is zero for every m>0. Removing exactly this endpoint is necessary for independence of the full indexed family.
-/
theorem gainAfterConjugationIndependent (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 1 < k2) :
    AmplifierRealized k2 ∧
    KrausWellDefined (productKraus (amplifierKraus k2) (phaseKraus k1)) ∧
    LinearIndependent ℂ (productKraus (amplifierKraus k2) (phaseKraus k1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
