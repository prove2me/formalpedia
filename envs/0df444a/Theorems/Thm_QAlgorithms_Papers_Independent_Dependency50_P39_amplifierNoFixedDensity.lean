-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_amplifierNoFixedDensity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.amplifierNoFixedDensity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:37:20.400981+00:00
-- url     : https://prove2.me/theorems/d35ab0e6-14bc-485c-b071-717b0f5441c8
-- title:
--   Theorem 11: no amplifier fixed state
-- statement:
--   Let $\kappa>1$. The complete amplifier family $A_\ell(\kappa)$ defines a trace-norm-convergent map on every trace-class operator on $\ell^2(\mathbb N;\mathbb C)$. There is no normalized positive trace-class fixed density:
--
--   $$\forall\rho\ge0,\quad \operatorname{tr}\rho=1\ \Longrightarrow\ C_{2,\kappa}(\rho)\ne\rho.$$
--
--   The identity endpoint is excluded. No finite-energy or moment-existence restriction is added. The claim concerns all normal density operators.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 21, Theorem 11: no amplifier fixed state

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 11, PDF p.21: no normalized trace-class density is fixed by
an amplifier of gain strictly greater than one. This is not restricted to
Gaussian or finite-energy states. -/
theorem amplifierNoFixedDensity (k : ℝ) (hk : 1 < k) :
    AmplifierRealized k ∧ KrausWellDefined (amplifierKraus k) ∧
    ∀ X : FockOperator, IsDensity X →
      ¬ TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) X) X := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
