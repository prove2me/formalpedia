-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P05_e7_zorn_adjoint
-- name    : QAlgorithms.Papers.Independent.Support21.P05.e7_zorn_adjoint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:35:56.354326+00:00
-- url     : https://prove2.me/theorems/fcfc67ba-ddbe-44ef-a7fd-8b0507fc2e48
-- title:
--   The E7 adjoint Zorn realization
-- statement:
--   All parameters are over the base field $\mathbb C$. Here $A=M_2(\mathbb C)$, the complexified quaternions, with $\bar q=\operatorname{tr}_2(q)I_2-q$ and scalar part $\operatorname{tr}_2(q)/2$; the central space is $\{h\in M_3(A):t(h)=0\}$, imposing only the single scalar trace constraint.
--
--   For the associative composition algebra $A$ specified below, let $\bar q$ denote its composition conjugation, fixing $\mathbb C$, and let $p(q)=(q+\bar q)/2$ denote its scalar part. Put $J=H_3(A)=\{x:x^\dagger=x\}$, where $\dagger$ is composition-conjugate transpose. Define $x\cdot y=(xy+yx)/2$, $t(x)=p(\operatorname{tr}x)$, and $t(x,y)=t(x\cdot y)$. Use the unhalved polarization
--
--   $$x\#y=xy+yx-t(x)y-t(y)x+(t(x)t(y)-t(x,y))I_3.$$
--
--   For triples $X,Y$ of Jordan matrices, set $(X\times Y)_i=\sum_{jk}\epsilon_{ijk}(X_j\#Y_k)$, with $\epsilon_{123}=1$. Define $d_0(X,Y)=\frac13\sum_i t(X_i,Y_i)I_3-(t(X_i,Y_j))_{ij}$ and $d_1(X,Y)=\frac13\sum_i t(X_i,Y_i)I_3-\sum_iX_iY_i$. On coordinates $(a,h,X^+,X^-)$, with $a\in\mathfrak{sl}_3(\mathbb C)$ and $h$ in the stated central space, the Zorn bracket of $x=(a,h,X^+,X^-)$ and $y=(b,k,Y^+,Y^-)$ has four components
--
--   $$
--   \begin{aligned}
--   C_0&=[a,b]+d_0(X^+,Y^-)-d_0(Y^+,X^-),\\
--   C_1&=[h,k]+d_1(X^+,Y^-)-d_1(Y^+,X^-),\\
--   C_+&=aY^+-bX^++hY^++Y^+h^\dagger-kX^+-X^+k^\dagger+X^-\times Y^-,\\
--   C_-&=X^-b-Y^-a-h^\dagger Y^--Y^-h+k^\dagger X^-+X^-k+X^+\times Y^+.
--   \end{aligned}
--   $$
--
--   External matrix multiplication acts on the three vector indices; products by $h,k$ act componentwise on Jordan matrices. The bottom-right block is $-I_3\otimes h^\dagger$, so it is determined by these coordinates. All opposite spaces are independent complex-linear copies with the displayed contragredient action.
--
--   There exists a complex-linear bijection $\rho$ from the independently Serre-defined complex exceptional Lie algebra $\mathfrak E_7$ to the full coordinate space $Z$ above, such that
--
--   $$\rho([u,v])=[\rho(u),\rho(v)]_Z\qquad(u,v\in\mathfrak E_7).$$
--
--   This realizes the adjoint algebra by the specified special bracket. The bijection retains all central and Jordan slots; Jacobi is a conclusion, not an assumed invariant of the coordinate model.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations, arXiv:1403.5120v2, PDF p. 21, §7: E7 Zorn realization

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P05

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

/-- §7 and §8, PDF pp. 20–25: (7.1) realizes the adjoint of complex E7.
The central sl3(Q) has only its scalar trace removed; H3(Q) is 15-dimensional. -/
theorem e7_zorn_adjoint :
    ∃ rho : LieAlgebra.e₇ ℂ ≃ₗ[ℂ] E7Coordinates,
      ∀ x y, associativeValue (rho ⁅x, y⁆) =
        associativeBracket quaternionConjugation quaternionScalarPart
          (associativeValue (rho x)) (associativeValue (rho y)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P05

end
