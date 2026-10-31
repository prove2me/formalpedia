-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_normalized_determinant_degree
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.normalized_determinant_degree
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:21:12.96943+00:00
-- url     : https://prove2.me/theorems/84bf38df-f0d8-474f-bf32-e2ff7734bda9
-- title:
--   Corollary 12: normalized complex-linear determinant degree
-- statement:
--   Let $n\ge1$ and $\psi\in SP(n)$, meaning a continuous symplectic path on $[0,1]$ with $\psi(0)=I$ and no eigenvalue $1$ at $\psi(1)$. Let $\widetilde\psi$ be any continuous extension to $[0,2]$ agreeing on $[0,1]$, avoiding eigenvalue $1$ on $[1,2]$, and ending at either standard representative $W^+$ or $W^-$. Put $C_A=(A-J_0AJ_0)/2$, the complex-linear part relative to $J_0=\left(\begin{smallmatrix}0&-I\\I&0\end{smallmatrix}\right)$, and define $\widehat\rho(A)=\det_{\mathbb C}(C_A)/|\det_{\mathbb C}(C_A)|$. Then
--
--   $$\mu_{CZ}(\psi)=\deg(\widehat\rho^{\,2}\circ\widetilde\psi).$$
--
--   Invertibility of $C_A$ follows from symplecticity, so no invertibility premise is added. This gives the normalized complex-linear determinant formula alone.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 8, Corollary 12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Corollary 12, PDF pp.8-9: the degree formula alone.
Invertibility of the complex-linear part is a proved fact, not a premise. -/
theorem normalized_determinant_degree {n : ℕ} (hn : 1 ≤ n)
    (p e : ℝ → GroupedRealMatrix n) (hp : IsAdmissible p 1) (he : IsExtension p e) :
    conleyZehnder p 1 = winding (fun t => normalizedDet (e t)^2) 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
