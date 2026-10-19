-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_phaseNonclassicalityBreaking
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.phaseNonclassicalityBreaking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:27:38.566635+00:00
-- url     : https://prove2.me/theorems/4fc85e65-3eaf-43f1-8cbc-079a59bcc603
-- title:
--   Theorem 3: nonclassicality breaking
-- statement:
--   Let $\kappa>0$ and let $\rho$ be any positive trace-class operator of trace one on $H=\ell^2(\mathbb N;\mathbb C)$. Let $T_\ell(\kappa)$ be the phase-conjugator Kraus family from Eq. (3.11). Its output is a classical state:
--
--   $$D_\kappa(\rho)=\sum_{\ell\ge0}T_\ell(\kappa)\rho T_\ell(\kappa)^\dagger
--   =\int_{\mathbb C}|\alpha\rangle\langle\alpha|\,\mu(d\alpha),$$
--
--   where the sum converges in trace norm and $\mu$ is a positive Borel probability measure. The coherent states $|\alpha\rangle$ are normalized. Singular measures are allowed, so this is the full notion of optical classicality. The assertion concerns every input density, not only Gaussian states.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 10, Theorem 3: nonclassicality breaking

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 3, PDF pp.9–10: phase conjugation maps every density to a
classical coherent-state mixture, allowing positive singular measures. -/
theorem phaseNonclassicalityBreaking (k : ℝ) (hk : 0 < k) :
    CoherentRealized ∧ KrausWellDefined (phaseKraus k) ∧
    ∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (phaseKraus k ell) X) Y ∧ IsClassical Y := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
