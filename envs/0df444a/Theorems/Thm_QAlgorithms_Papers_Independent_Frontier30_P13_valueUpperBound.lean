-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P13_valueUpperBound
-- name    : QAlgorithms.Papers.Independent.Frontier30.P13.valueUpperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:18:06.816977+00:00
-- url     : https://prove2.me/theorems/9514c792-f02a-4a39-9099-1321babd7cce
-- title:
--   A symplectic upper bound on the Gaussian entanglement scale
-- statement:
--   Let $\gamma$ be a finite physical covariance on two nonempty finite mode sets $A$ and $B$, with vacuum covariance equal to the identity. Reverse the momentum coordinates of $A$ using $L=\Lambda_A\oplus I_B$ and put $\widetilde\gamma=L\gamma L$. Let $\lambda_{\min}(\gamma)$ be the smallest positive symplectic eigenvalue of this positive definite matrix. Equivalently, it is the smallest positive real root $t$ of $\det(\widetilde\gamma-itJ)=0$. For the variational scale $V$, defined by physical local covariance lower bounds, one has
--
--   $$V(\gamma)\le\min\{\lambda_{\min}(\gamma),1\}.$$
--
--   The bound applies also when the partially transposed covariance satisfies the uncertainty inequality; no NPT assumption is imposed.
-- source:
--   The characterization of Gaussian operations and Distillation of Gaussian States, arXiv:quant-ph/0204085v4, PDF p. 6, Appendix A(2), Eq.(A3): symplectic upper bound

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

/-- Appendix A, PDF pp.6–7, Eq.(A3): the smallest partially transposed
symplectic eigenvalue, clamped by 1, bounds V above, including PPT inputs. -/
theorem valueUpperBound {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ)
    (hG : physicalCovariance G (bipJ A B)) :
    valueV G ≤ min (lambdaMin G) 1 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P13

end
