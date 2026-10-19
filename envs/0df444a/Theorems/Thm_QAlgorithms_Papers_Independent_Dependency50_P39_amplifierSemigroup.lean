-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_amplifierSemigroup
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.amplifierSemigroup
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:38:52.180971+00:00
-- url     : https://prove2.me/theorems/b2b99d69-eb35-40e0-be4b-be25ea21a222
-- title:
--   Eq.(5.25),(5.30): amplifier semigroup
-- statement:
--   Let $\kappa_1,\kappa_2>1$. For the complete countable amplifier channels on the full oscillator trace class,
--
--   $$C_{2,\kappa_2}\circ C_{2,\kappa_1}=C_{2,\kappa_1\kappa_2}
--   =C_{2,\kappa_1}\circ C_{2,\kappa_2}.$$
--
--   In either order the products of the explicit amplifier Kraus operators are strongly complete, and their trace-norm sum on every trace-class input agrees with the single-family sum at the product gain. This states both the semigroup law and commutativity of these maps.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 23, Eq.(5.25),(5.30): amplifier semigroup

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF pp.22–23 Eqs.(5.25),(5.30): both amplifier composition orders give
the same trace-class map, with product gain. -/
theorem amplifierSemigroup (k1 k2 : ℝ) (h1 : 1 < k1) (h2 : 1 < k2) :
    AmplifierRealized k1 ∧ AmplifierRealized k2 ∧ AmplifierRealized (k1 * k2) ∧
    KrausEquivalent (productKraus (amplifierKraus k2) (amplifierKraus k1))
      (amplifierKraus (k1 * k2)) ∧
    KrausEquivalent (productKraus (amplifierKraus k1) (amplifierKraus k2))
      (amplifierKraus (k1 * k2)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
