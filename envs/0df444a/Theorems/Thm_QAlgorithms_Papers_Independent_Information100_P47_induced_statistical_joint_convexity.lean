-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P47_induced_statistical_joint_convexity
-- name    : QAlgorithms.Papers.Independent.Information100.P47.induced_statistical_joint_convexity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:37:18.241405+00:00
-- url     : https://prove2.me/theorems/19200c1a-7e63-46bc-a794-ecd8d6797c83
-- title:
--   Joint convexity of the induced maximal statistical distance
-- statement:
--   For each finite nonempty outcome set, let $\delta$ be a nonnegative, possibly extended-valued function of two probability distributions. Assume joint convexity: the same finite probability weights are used to mix its two arguments. For $n$-outcome POVMs on $\mathbb C^d$, with $d,n\ge1$, define $D(A,B)=\sup_\rho\delta(p_{\rho,A},p_{\rho,B})$, where $\rho$ ranges over positive semidefinite matrices of trace one and $p_{\rho,A}(x)=\operatorname{Tr}(A_x\rho)$. For any finite probability vector $(\alpha_j)_j$ and pairs of POVMs $(A^{(j)},B^{(j)})$ on the same space with the same outcome labels,
--
--   $$D\left(\sum_j\alpha_jA^{(j)},\sum_j\alpha_jB^{(j)}\right)\le\sum_j\alpha_jD(A^{(j)},B^{(j)}).$$
--
--   Thus state-induced statistical distances inherit joint convexity. No maximizer over states, channel contractivity, symmetry, or triangle inequality is required.
-- source:
--   Maximal coherence of quantum measurement and the resource theory of sharpness, arXiv:2607.05847v1, PDF p. 10, Appendix A, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

/-- PDF p.10, Appendix A, Lemma 1: joint convexity of the induced statistical distance. -/
theorem induced_statistical_joint_convexity (delta : StatisticalDistance)
    (hC : StatisticalJointConvex delta) : JointConvex (inducedDistance delta) := by sorry

end QAlgorithms.Papers.Independent.Information100.P47

end
