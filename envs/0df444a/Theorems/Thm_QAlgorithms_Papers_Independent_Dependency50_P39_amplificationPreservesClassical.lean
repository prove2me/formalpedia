-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_amplificationPreservesClassical
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.amplificationPreservesClassical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:36:11.985633+00:00
-- url     : https://prove2.me/theorems/1d3007f2-fa3d-4106-a3cc-0ac3d69e527d
-- title:
--   Corollary 2: amplification does not generate nonclassicality
-- statement:
--   Let $\kappa>1$ and let $\rho$ be any density on the full oscillator Fock space. Let $\rho'=C_{2,\kappa}(\rho)$ be the trace-norm output of the explicit amplifier family $A_\ell(\kappa)$. Then
--
--   $$\rho\text{ classical}\quad\Longrightarrow\quad\rho'\text{ classical}.$$
--
--   Classicality means a positive probability-measure mixture of normalized coherent projectors, allowing singular measures. The complete countable map is well defined on every trace-class operator. This corollary asserts only the stated implication.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 21, Corollary 2: amplification does not generate nonclassicality

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Corollary 2, PDF p.21: amplification takes classical inputs to classical
outputs. No converse preserving all input nonclassicality is asserted. -/
theorem amplificationPreservesClassical (k : ℝ) (hk : 1 < k) :
    CoherentRealized ∧ AmplifierRealized k ∧ KrausWellDefined (amplifierKraus k) ∧
    ∀ X : FockOperator, IsDensity X → ∃ Y : FockOperator,
      TraceHasSum (fun ell => krausTerm (amplifierKraus k ell) X) Y ∧
      IsDensity Y ∧ (IsClassical X → IsClassical Y) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
