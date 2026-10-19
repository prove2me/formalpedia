-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P13_valueDomain
-- name    : QAlgorithms.Papers.Independent.Frontier30.P13.valueDomain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:16:59.603517+00:00
-- url     : https://prove2.me/theorems/6863c2c7-2ead-43b6-8ceb-8d3f513ea274
-- title:
--   The Gaussian entanglement scale is positive and attained
-- statement:
--   Let $A$ and $B$ be nonempty finite sets of bosonic modes. In interleaved quadrature coordinates, let $J=J_A\oplus J_B$, with each single-mode block $\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$. Let $\gamma$ be a finite real symmetric covariance matrix satisfying $\gamma-iJ\succeq0$, in the convention that vacuum covariance is the identity. Define $F_\gamma$ to be the set of $p\in[0,1]$ for which physical local covariance matrices $\gamma_A,\gamma_B$ satisfy $\gamma\succeq p(\gamma_A\oplus\gamma_B)$, and put $V(\gamma)=\sup F_\gamma$. Then
--
--   $$0<V(\gamma)\le1,\qquad V(\gamma)\in F_\gamma,\qquad \forall p\in F_\gamma,\ p\le V(\gamma).$$
--
--   Thus the variational scale used in the paper is a maximum, without assuming that the state is separable.
-- source:
--   The characterization of Gaussian operations and Distillation of Gaussian States, arXiv:quant-ph/0204085v4, PDF p. 5, Appendix A, Eq.(A1): well-defined attained V for finite CMs

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

/-- Appendix A, PDF p.6, Eq.(A1); Section IVB, PDF p.5: the largest feasible
scale exists and satisfies 0 < V <= 1 for finite physical CMs. Separability
and the optimizing local covariance witnesses are not assumptions. -/
theorem valueDomain {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ)
    (hG : physicalCovariance G (bipJ A B)) :
    0 < valueV G ∧ valueV G ≤ 1 ∧
    IsGreatest {p | feasibleScale G p} (valueV G) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P13

end
