-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_twoConjugatorsIndependent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.twoConjugatorsIndependent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:41:32.905986+00:00
-- url     : https://prove2.me/theorems/079c8ad4-a9b3-4f55-b661-cdc3aad25e1f
-- title:
--   §IX.III: two conjugators
-- statement:
--   Let $\kappa_1,\kappa_2>0$. Two successive phase conjugators on the full Fock space have the complete linearly independent countable product family
--
--   $$\{T_m(\kappa_2)T_n(\kappa_1):(m,n)\in\mathbb N^2\}.$$
--
--   The first displayed factor acts after the second. The family has strong Kraus normalization and gives a trace-norm sum for every trace-class input. Actual operator composition specifies the two shift directions, avoiding the repeated dyad printed in the second branch of Eq. (9.3).
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 31, §IX.III: two conjugators

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.31 §IX.III: two phase conjugators have independent product Kraus
operators. Actual operator composition avoids the repeated-shift typo in (9.3). -/
theorem twoConjugatorsIndependent (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) :
    KrausWellDefined (productKraus (phaseKraus k2) (phaseKraus k1)) ∧
    LinearIndependent ℂ (productKraus (phaseKraus k2) (phaseKraus k1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
