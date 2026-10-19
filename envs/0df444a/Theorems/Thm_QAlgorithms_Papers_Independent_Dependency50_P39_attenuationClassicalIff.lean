-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_attenuationClassicalIff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.attenuationClassicalIff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:31:02.650994+00:00
-- url     : https://prove2.me/theorems/e9b43613-17fa-4840-9e8e-9c3512667c22
-- title:
--   Corollary 1: attenuation preserves classicality in both directions
-- statement:
--   Let $0<\kappa<1$ and let $\rho$ be any density on $\ell^2(\mathbb N;\mathbb C)$. Let $\rho'=C_{1,\kappa}(\rho)$ be the trace-norm output of the explicit attenuator family $B_\ell(\kappa)$ of Eq. (4.6). Then
--
--   $$\rho'\text{ is classical}\quad\Longleftrightarrow\quad\rho\text{ is classical}.$$
--
--   A state is classical when it is a positive probability-measure mixture of normalized coherent projectors; the measure may be singular. The vacuum-replacer endpoint $\kappa=0$ is excluded. This is preservation of classicality in both directions.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 15, Corollary 1: attenuation preserves classicality in both directions

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Corollary 1, PDF p.15: nonzero attenuation preserves classicality in
both directions, on all normalized trace-class input densities. -/
theorem attenuationClassicalIff (k : ℝ) (hk : 0 < k) (hku : k < 1) :
    CoherentRealized ∧ AttenuatorRealized k ∧ KrausWellDefined (attenuatorKraus k) ∧
    ∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (attenuatorKraus k ell) X) Y ∧
      IsDensity Y ∧ (IsClassical Y ↔ IsClassical X) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
