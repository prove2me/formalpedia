-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_arbitrary_path_endpoint_formula
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.arbitrary_path_endpoint_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:19:48.007983+00:00
-- url     : https://prove2.me/theorems/44564a21-5391-4bfe-ba7e-70d1ea652c00
-- title:
--   Theorem 3: endpoint signature formula for arbitrary continuous paths
-- statement:
--   Let $n\ge1$ and let $\psi:[0,1]\to\operatorname{Sp}(2n,\Omega_0)$ be any continuous path. At each endpoint split off its generalized $1$-eigenspace symplectically, writing $\psi(i)=\psi^\star(i)\diamond\psi^{(1)}(i)$, where the first block has no eigenvalue $1$. Let $\Psi:[-1,2]\to\operatorname{Sp}(2n,\Omega_0)$ be continuous, agree with $\psi$ on $[0,1]$, and satisfy the following endpoint conditions in those bases. At $-1/2$ and $3/2$ the respective $1$-blocks are $H=\operatorname{diag}(e^{-1}I,eI)$; on $[-1/2,0]$ and $[1,3/2]$ the star block is fixed and the other block has only positive real eigenvalues. The values $\Psi(-1)$ and $\Psi(2)$ are independently $W^+$ or $W^-$, and $\Psi$ has no eigenvalue $1$ on the two outer intervals. Let $r$ be continuous and circle-valued on the symplectic group, agree with $\det_{\mathbb C}$ on $U(n)$, satisfy $r(W^-)\in\{1,-1\}$, and obey $\deg(r^2\circ\psi_{2-})=n-1$. Here $W^+=-I$, $W^-=\operatorname{diag}(2,-1,\ldots,-1,1/2,-1,\ldots,-1)$, and $\psi_{2-}(t)=\exp(t\pi J_0S^-)$ with $J_0=\left(\begin{smallmatrix}0&-I\\I&0\end{smallmatrix}\right)$, diagonal blocks of $S^-$ equal to $\operatorname{diag}(0,1,\ldots,1)$ and both off-diagonal blocks equal to $\operatorname{diag}(-\log(2)/\pi,0,\ldots,0)$. Then
--
--   $$\mu_{RS}(\psi)=\deg(r^2\circ\Psi)+\frac12\sum_{k=1}^{2n}\operatorname{Sign}\widehat Q_k^{\psi(0)}-\frac12\sum_{k=1}^{2n}\operatorname{Sign}\widehat Q_k^{\psi(1)}.$$
--
--   For a symplectic matrix $A$, $\widehat Q_k^A(v,w)=\Omega_0((A-I)^kv,(A-I)^{k-1}w)$ on $\ker(A-I)^{2k}$. Signature means positive minus negative inertia, including radicals. The infinite-looking source sums terminate beyond the ambient dimension. Degree is taken on the whole interval $[-1,2]$, represented by $t\mapsto\Psi(t-1)$ on $[0,3]$. This formula handles arbitrary, possibly degenerate endpoints without a regular-crossing premise.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 3, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Theorem 3, PDF pp.3-4 and p.23: arbitrary continuous paths and both endpoint
signature corrections. No SP(n) endpoint assumptions apply to this theorem. -/
theorem arbitrary_path_endpoint_formula {n : ℕ} (hn : 1 ≤ n)
    (p e : ℝ → GroupedRealMatrix n) (hp : IsPath p 1)
    (D0 : EndpointSplitting (p 0)) (D1 : EndpointSplitting (p 1))
    (he : IsProlongation p e D0 D1)
    (r : GroupedRealMatrix n → ℂ) (hc : ContinuousOn r {A | IsSymplectic A})
    (hcircle : ∀ A, IsSymplectic A → ‖r A‖ = 1)
    (hdet : ∀ A, IsUnitaryReal A → r A = complexActionDet A)
    (hw : r (wMinus n) = 1 ∨ r (wMinus n) = -1)
    (href : winding (fun t => r (referenceMinus n t)^2) 1 = (n : ℤ)-1) :
    robbinSalamon p = (prolongationDegree r e : ℚ) +
      (endpointSignatureSum (p 0) 1 : ℚ)/2 -
        (endpointSignatureSum (p 1) 1 : ℚ)/2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
