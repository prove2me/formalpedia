-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_attenuatorUniqueFixedDensity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorUniqueFixedDensity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:31:34.960978+00:00
-- url     : https://prove2.me/theorems/78bef52f-e969-4480-8b7f-5a90efcf4028
-- title:
--   Theorem 7: vacuum is the only attenuator fixed point
-- statement:
--   Let $0<\kappa<1$ and let $\rho$ be any positive trace-class operator of trace one on $H=\ell^2(\mathbb N;\mathbb C)$. The channel defined by the explicit attenuator Kraus family is well defined on every trace-class operator, and
--
--   $$C_{1,\kappa}(\rho)=\rho\quad\Longleftrightarrow\quad\rho=|0\rangle\langle0|.$$
--
--   The Kraus sum converges in trace norm. No finite-energy, Gaussianity, or cumulant-existence hypothesis is imposed. The assertion identifies every fixed density and includes invariance of the vacuum.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 16, Theorem 7: vacuum is the only attenuator fixed point

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 7, PDF pp.15–16: vacuum is exactly the fixed density of the
nonidentity attenuator. Arbitrary normalized trace-class inputs are included,
without assuming that moments or cumulants exist. -/
theorem attenuatorUniqueFixedDensity (k : ℝ) (hk : 0 < k) (hku : k < 1) :
    AttenuatorRealized k ∧ KrausWellDefined (attenuatorKraus k) ∧
    IsDensity (fockDyad 0 0) ∧
    ∀ X : FockOperator, IsDensity X →
      (TraceHasSum (fun ell => krausTerm (attenuatorKraus k ell) X) X ↔
        X = fockDyad 0 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
