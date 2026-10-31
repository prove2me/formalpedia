-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_alternative_rotation_and_concrete_degrees
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.alternative_rotation_and_concrete_degrees
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:19:04.886676+00:00
-- url     : https://prove2.me/theorems/80ce82a8-7d2f-42e7-ac21-602e58d8f2d0
-- title:
--   Theorem 1: alternative rotation maps and both concrete degree formulae
-- statement:
--   Let $n\ge1$, let $\psi:[0,1]\to\operatorname{Sp}(2n,\Omega_0)$ be continuous with $\psi(0)=I$ and $\det(\psi(1)-I)\ne0$, and let $\widetilde\psi:[0,2]\to\operatorname{Sp}(2n,\Omega_0)$ agree with $\psi$, have no eigenvalue $1$ on $[1,2]$, and end at $W^+=-I$ or $W^-=\operatorname{diag}(2,-1,\ldots,-1,1/2,-1,\ldots,-1)$. For every continuous circle-valued $r$ agreeing with $\det_{\mathbb C}$ on $U(n)$, satisfying $r(W^-)\in\{1,-1\}$ and $\deg(r^2\circ\psi_{2-})=n-1$, one has
--
--   $$\mu_{CZ}(\psi)=\deg(r^2\circ\widetilde\psi)=\deg((\det_{\mathbb C}\circ U)^2\circ\widetilde\psi)=\deg(\widehat\rho^{\,2}\circ\widetilde\psi).$$
--
--   Here $\psi_{2-}(t)=\exp(t\pi J_0S^-)$, where the $xx$ and $yy$ diagonal blocks of $S^-$ are $\operatorname{diag}(0,1,\ldots,1)$ and both off-diagonal blocks are $\operatorname{diag}(-\log(2)/\pi,0,\ldots,0)$. Also $J_0=\left(\begin{smallmatrix}0&-I\\I&0\end{smallmatrix}\right)$, $U(A)=A P^{-1}$ for the positive symmetric square root $P$ of $A^\tau A$, and $\widehat\rho(A)=\det_{\mathbb C}(C_A)/|\det_{\mathbb C}(C_A)|$ with $C_A=(A-J_0AJ_0)/2$. Degree has the positive-turn orientation. These are three ways to compute the same integer index; the two concrete formulae require no additional hypotheses.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 2, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Theorem 1, PDF p.2 (proved pp.7-9): all three degree formulae.
The polar and normalized-determinant clauses have no extra premises. -/
theorem alternative_rotation_and_concrete_degrees {n : ℕ} (hn : 1 ≤ n)
    (p e : ℝ → GroupedRealMatrix n) (hp : IsAdmissible p 1) (he : IsExtension p e) :
    (∀ r : GroupedRealMatrix n → ℂ,
      ContinuousOn r {A | IsSymplectic A} →
      (∀ A, IsSymplectic A → ‖r A‖ = 1) →
      (∀ A, IsUnitaryReal A → r A = complexActionDet A) →
      (r (wMinus n) = 1 ∨ r (wMinus n) = -1) →
      winding (fun t => r (referenceMinus n t)^2) 1 = (n : ℤ)-1 →
      conleyZehnder p 1 = winding (fun t => r (e t)^2) 2) ∧
    conleyZehnder p 1 = winding (fun t => complexActionDet (polarU (e t))^2) 2 ∧
    conleyZehnder p 1 = winding (fun t => normalizedDet (e t)^2) 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
