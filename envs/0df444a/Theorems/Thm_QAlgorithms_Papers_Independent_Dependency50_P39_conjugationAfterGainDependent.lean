-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_conjugationAfterGainDependent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.conjugationAfterGainDependent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:43:48.939788+00:00
-- url     : https://prove2.me/theorems/d09d400e-e0e2-400f-83f5-db811a093940
-- title:
--   §IX.VII: conjugation after gain
-- statement:
--   Let $\kappa_2>0$ and $\kappa_1\ge1$. The product family
--
--   $$\{T_m(\kappa_2)A_n(\kappa_1):(m,n)\in\mathbb N^2\}$$
--
--   on the full Fock space is linearly dependent, while its complete trace-class Kraus map is the quantum-limited phase conjugator $D(\kappa_2\kappa_1)$. Both the product and the single-family sums converge in trace norm to the same output for every trace-class input. At the identity-gain endpoint the unreduced indexed family still contains zero operators and remains dependent.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 33, §IX.VII: conjugation after gain

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.33 §IX.VII: conjugation after gain is redundant and implements
D(k2*k1); the identity gain endpoint still has zeros in the full indexed family. -/
theorem conjugationAfterGainDependent (k1 k2 : ℝ) (h1 : 1 ≤ k1) (h2 : 0 < k2) :
    AmplifierRealized k1 ∧
    ¬ LinearIndependent ℂ (productKraus (phaseKraus k2) (amplifierKraus k1)) ∧
    KrausEquivalent (productKraus (phaseKraus k2) (amplifierKraus k1))
      (phaseKraus (k2 * k1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
