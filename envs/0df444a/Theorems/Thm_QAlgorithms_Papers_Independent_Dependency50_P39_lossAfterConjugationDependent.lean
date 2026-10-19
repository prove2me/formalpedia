-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_lossAfterConjugationDependent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.lossAfterConjugationDependent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:42:54.84698+00:00
-- url     : https://prove2.me/theorems/505c4120-015c-4885-894e-8ce6b30150c5
-- title:
--   §IX.V: loss after conjugation
-- statement:
--   Let $\kappa_1>0$ and $0\le\kappa_2\le1$, and set $W_{mn}=B_m(\kappa_2)T_n(\kappa_1)$ on the full Fock space. Then
--
--   $$W_{mn}=0\ (m>n),\qquad W_{mm}\in\mathbb C\,|0\rangle\langle0|.$$
--
--   The full indexed family is linearly dependent. It nevertheless defines exactly the same complete trace-class map as $\{T_\ell(\kappa_2\kappa_1)\}$, with trace-norm convergence of both sums on every trace-class input. At product parameter zero, $T_\ell(0)$ means the vacuum-replacer family $|0\rangle\langle\ell|$, rather than a reciprocal expression.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 32, §IX.V: loss after conjugation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.32 §IX.V: loss after conjugation is redundant, with the stated zero
products and vacuum-projector diagonal products, and implements D(k2*k1).
At k2=0, D(0) means the vacuum-replacer family, not a reciprocal formula. -/
theorem lossAfterConjugationDependent (k1 k2 : ℝ) (h1 : 0 < k1)
    (h2 : 0 ≤ k2) (h2u : k2 ≤ 1) :
    AttenuatorRealized k2 ∧
    (∀ m n : ℕ, n < m →
      productKraus (attenuatorKraus k2) (phaseKraus k1) (m, n) = 0) ∧
    (∀ m : ℕ, ∃ c : ℂ,
      productKraus (attenuatorKraus k2) (phaseKraus k1) (m, m) = c • fockDyad 0 0) ∧
    ¬ LinearIndependent ℂ (productKraus (attenuatorKraus k2) (phaseKraus k1)) ∧
    KrausEquivalent (productKraus (attenuatorKraus k2) (phaseKraus k1))
      (phaseKraus (k2 * k1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
