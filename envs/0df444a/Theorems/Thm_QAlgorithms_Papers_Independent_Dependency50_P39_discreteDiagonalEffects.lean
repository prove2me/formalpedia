-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_discreteDiagonalEffects
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.discreteDiagonalEffects
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:44:30.973984+00:00
-- url     : https://prove2.me/theorems/4526c289-69a1-434e-9ab0-f0c0e10b8cd9
-- title:
--   §IX Remark 3: simultaneous Fock diagonality in the discrete cases
-- statement:
--   On the full oscillator Fock space, let $W_\ell$ be any of the explicit canonical phase-conjugator, attenuator, or amplifier Kraus families in its permitted domain, including the attenuator and amplifier endpoints. The effects of each family and of every ordered pair of these families are diagonal in the same Fock basis. More explicitly, for either a single operator $V=W_\ell$ or a product $V=W_mW'_n$,
--
--   $$\langle r|V^\dagger V|s\rangle=0\qquad(r\ne s).$$
--
--   This includes all discrete noisy product families used in Theorem 14. The statement is about bounded effects in a genuine orthonormal basis; it does not replace the generalized-position claim in deferred Theorem 15. The continuous $B_1$ realization is handled by its separately deferred node.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 34, §IX Remark 3: simultaneous Fock diagonality in the discrete cases

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.34 Remark 3: all discrete canonical Kraus effects and the effects of
their displayed products are diagonal in the same Fock basis. This makes no
claim about the generalized-position effects in deferred Theorem 15. -/
theorem discreteDiagonalEffects (F G : DiscreteFamily) :
    DiscreteRealized F ∧ DiscreteRealized G ∧
    (∀ ell, FockDiagonalEffect (discreteKraus F ell)) ∧
    (∀ p : ℕ × ℕ,
      FockDiagonalEffect (productKraus (discreteKraus F) (discreteKraus G) p)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
