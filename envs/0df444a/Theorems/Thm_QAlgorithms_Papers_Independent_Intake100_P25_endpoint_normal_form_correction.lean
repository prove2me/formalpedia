-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_endpoint_normal_form_correction
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.endpoint_normal_form_correction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:22:40.334556+00:00
-- url     : https://prove2.me/theorems/8c0f437a-cf41-49c4-a69a-7342ef845426
-- title:
--   Theorem 28: endpoint normal-form sign correction
-- statement:
--   Let $n\ge1$ and let $\psi:[0,1]\to\operatorname{Sp}(2n,\Omega_0)$ be continuous with arbitrary endpoints. Choose endpoint symplectic splittings into the generalized $1$-eigenspace and its non-$1$ part. Choose actual Proposition 25 normal forms of the two endpoints on those generalized eigenspaces, with signs $d_i^{(0)}$ and $d_j^{(1)}$. Empty generalized eigenspaces and empty sign sums are permitted. Let $\Psi:[-1,2]\to\operatorname{Sp}(2n,\Omega_0)$ agree with $\psi$ on $[0,1]$. On $[-1/2,0]$ and $[1,3/2]$, keep each star block fixed and let the other block have only positive real eigenvalues; at $-1/2$ and $3/2$ that block must be $\operatorname{diag}(e^{-1}I,eI)$. Require independent $W^\pm$ endpoints at $-1,2$, and no eigenvalue $1$ on $[-1,-1/2]\cup[3/2,2]$. Then, with Definition 5 spectral rotation $\rho$,
--
--   $$\mu_{RS}(\psi)=\deg(\rho^2\circ\Psi)+\frac12\sum_i d_i^{(0)}-\frac12\sum_j d_j^{(1)}.$$
--
--   The degree uses the complete translated interval $[0,3]$. The signs are derived from normal forms of these endpoint matrices, rather than arbitrary lists. This is the normal-form version of the endpoint signature formula. The same formula holds with $\rho$ replaced by every continuous circle-valued $r$ agreeing with the complex determinant on $U(n)$, satisfying $r(W^-)\in\{1,-1\}$ and $\deg(r^2\circ\psi_{2-})=n-1$, exactly as in Proposition 10. Both the fixed spectral formula and this universally quantified alternative-map clause are included.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 23, Theorem 28

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Theorem 28 and its following sentence, PDF pp.22-23: correction signs
come from actual normal forms, including empty generalized 1-spaces.
The formula holds for the spectral rotation and every alternative rotation
satisfying Proposition 10, as explicitly stated immediately after the formula. -/
theorem endpoint_normal_form_correction {n : ℕ} (hn : 1 ≤ n)
    (p e : ℝ → GroupedRealMatrix n) (hp : IsPath p 1)
    (D0 : EndpointSplitting (p 0)) (D1 : EndpointSplitting (p 1))
    (N0 : NormalFormData (p 0) 1) (N1 : NormalFormData (p 1) 1)
    (he : IsProlongation p e D0 D1) :
    (robbinSalamon p = (prolongationDegree spectralRotation e : ℚ) +
      (normalSignSum N0 : ℚ)/2 - (normalSignSum N1 : ℚ)/2) ∧
    (∀ r : GroupedRealMatrix n → ℂ,
      ContinuousOn r {A | IsSymplectic A} →
      (∀ A, IsSymplectic A → ‖r A‖ = 1) →
      (∀ A, IsUnitaryReal A → r A = complexActionDet A) →
      (r (wMinus n) = 1 ∨ r (wMinus n) = -1) →
      winding (fun t => r (referenceMinus n t)^2) 1 = (n : ℤ)-1 →
      robbinSalamon p = (prolongationDegree r e : ℚ) +
        (normalSignSum N0 : ℚ)/2 - (normalSignSum N1 : ℚ)/2) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
