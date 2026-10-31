-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_jordanWigner_representations
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.jordanWigner_representations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:48:38.122858+00:00
-- url     : https://prove2.me/theorems/c0ce0ce8-403b-4597-9fbf-c4f6a3726a24
-- title:
--   Explicit Jordan–Wigner CAR representations
-- statement:
--   In the ordered basis of $\mathbb C^2$, use $\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $\sigma_2=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$, and $\sigma_3=\operatorname{diag}(1,-1)$. On $(\mathbb C^2)^{\otimes n}$ let $I_j=\sigma_3^{(1)}\cdots\sigma_3^{(j)}$, with $I_0=1$. The tuple
--   $$\big(I_{j-1}\sigma_1^{(j)},I_{j-1}\sigma_2^{(j)}\big)_{j=1}^n$$
--   is a self-adjoint CAR tuple over $\mathbb R^{2n}$. Appending either $+I_n$ or $-I_n$ gives a CAR tuple over $\mathbb R^{2n+1}$. Here a tuple $(G_k)$ satisfies $G_kG_l+G_lG_k=2\delta_{kl}1$ and extends real linearly to the CAR representation.
--   The statement includes $n=0$, giving the two scalar one-generator representations.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 16, unnumbered jordan-wigner

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section FiniteCAR

/-- PDF p.16, Section 4.2: both even and both signed odd Jordan-Wigner tuples.
No particle cutoff: these are the source's finite-dimensional spin representations. -/
theorem jordanWigner_representations (n : ℕ) :
    MatrixCAR (jordanWignerEven n) ∧
      ∀ c : ℂ, c = 1 ∨ c = -1 → MatrixCAR (jordanWignerOdd n c) := by sorry

end FiniteCAR

end QAlgorithms.Papers.Independent.Intake100.P23

end
