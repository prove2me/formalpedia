-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_attenuatorNoFiniteRank
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorNoFiniteRank
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:32:53.448993+00:00
-- url     : https://prove2.me/theorems/f2796f93-2dd0-49bd-b023-4b9cfb3abd3a
-- title:
--   Theorem 8: no nonzero finite-rank operator in attenuator support
-- statement:
--   Let $0<\kappa<1$, and let $B_\ell(\kappa)$ be the bounded attenuator operators on the full oscillator space. Write $\operatorname{span}_{\mathbb C}\{B_\ell\}$ for their algebraic span, consisting of finite linear combinations. Then
--
--   $$0\ne M\in\operatorname{span}_{\mathbb C}\{B_\ell(\kappa):\ell\in\mathbb N\}
--   \quad\Longrightarrow\quad \dim_{\mathbb C}\operatorname{ran}M=\infty.$$
--
--   The attenuator channel is not entanglement breaking: its local action fails to produce a separable output on some ancillary bipartite density. The zero operator is excluded, and no topological closure of the Kraus span is taken. This is the source's stronger support assertion as well as its operational consequence.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 16, Theorem 8: no nonzero finite-rank operator in attenuator support

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Theorem 8, PDF p.16: every nonzero member of the algebraic Kraus span
has infinite-dimensional range. The zero operator is explicitly excluded. 
Printed: Theorem 8 says there is no finite rank operator in the support of the attenuator Kraus set.
Changed: Exclude the zero operator; use the algebraic complex span specified by the source proof.
Why: Zero is in every span and has finite rank. The proof selects the first nonzero coefficient, so the nonzero guard is the minimal correction.
-/
theorem attenuatorNoFiniteRank (k : ℝ) (hk : 0 < k) (hk1 : k < 1) :
    AttenuatorRealized k ∧
    (∀ M ∈ Submodule.span ℂ (Set.range (attenuatorKraus k)), M ≠ 0 →
      ¬ Module.Finite ℂ (LinearMap.range M.toLinearMap)) ∧
    ¬ IsCountableEntanglementBreaking (attenuatorKraus k) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
