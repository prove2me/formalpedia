-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P39_amplifierNoFiniteRank
-- name    : QAlgorithms.Papers.Independent.Dependency50.P39.amplifierNoFiniteRank
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:38:27.044153+00:00
-- url     : https://prove2.me/theorems/5bd0b126-5b79-43c4-b24a-1714309762ed
-- title:
--   §V entanglement-breaking remark: infinite Kraus rank
-- statement:
--   Let $\kappa>1$, and let $A_\ell(\kappa)$ be the bounded amplifier operators of Eq. (5.5) on the full Fock space. Then
--
--   $$0\ne M\in\operatorname{span}_{\mathbb C}\{A_\ell(\kappa):\ell\in\mathbb N\}
--   \quad\Longrightarrow\quad\dim_{\mathbb C}\operatorname{ran}M=\infty.$$
--
--   Here the span is algebraic, consisting of finite combinations. The amplifier channel is not entanglement breaking in the operational sense, which tests arbitrary ancillary bipartite densities and trace-norm separability. The assertion is stronger than excluding only rank-one members of the Kraus span.
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
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, PDF p. 22, §V entanglement-breaking remark: infinite Kraus rank

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.22, amplifier support remark: no nonzero finite-rank operator in
the algebraic span. No closure of the span and no natural-valued rank are used. 
Printed: The amplifier support remark says there exists no finite rank operator in the support of its Kraus set.
Changed: Exclude the zero operator; retain the algebraic span interpretation inherited from Theorem 8.
Why: Zero is an unavoidable finite-rank span element. The adjoint argument uses the nonzero version of Theorem 8.
-/
theorem amplifierNoFiniteRank (k : ℝ) (hk : 1 < k) :
    AmplifierRealized k ∧
    (∀ M ∈ Submodule.span ℂ (Set.range (amplifierKraus k)), M ≠ 0 →
      ¬ Module.Finite ℂ (LinearMap.range M.toLinearMap)) ∧
    ¬ IsCountableEntanglementBreaking (amplifierKraus k) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P39

end
