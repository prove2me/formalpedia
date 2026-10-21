-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P05_associative_zorn_jacobi
-- name    : QAlgorithms.Papers.Independent.Support21.P05.associative_zorn_jacobi
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:36:26.699628+00:00
-- url     : https://prove2.me/theorems/8cee0142-6e22-41cc-a0ec-2839a3bc066f
-- title:
--   Jacobi for the raw F4, E6 and E7 coordinate brackets
-- statement:
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
--   Consider separately (i) $A=\mathbb C$ with identity composition conjugation and central space $\mathfrak{sl}_3(\mathbb C)$, (ii) $A=\mathbb C\times\mathbb C$ with swapping conjugation and central matrices of zero full $A$-valued trace, and (iii) $A=M_2(\mathbb C)$ with $\bar q=\operatorname{tr}_2(q)I_2-q$ and central matrices of zero scalar trace. Their scalar parts are respectively $q$, $(q_++q_-)/2$, and $\operatorname{tr}_2(q)/2$. In all three cases each positive and negative vector component belongs to the corresponding $H_3(A)$.
--
--   For all three arbitrary admissible coordinate tuples $x,y,z$ in each of these spaces, the explicitly defined raw operation satisfies
--
--   $$[[x,y]_Z,z]_Z+[[y,z]_Z,x]_Z+[[z,x]_Z,y]_Z=0.$$
--
--   The identity applies to the three associative-entry realizations of F4, E6 and E7. It is asserted directly for the raw operations and does not assume a Lie structure on those operations. The Albert-algebra operator construction for E8 is a separate result.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations, arXiv:1403.5120v2, PDF p. 25, §8: Jacobi for F4,E6,E7 raw brackets

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P05

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

/-- §8, PDF pp. 22–25: Jacobi holds for all three explicit associative-entry brackets.
This is stated BEFORE installing any Lie instance on these coordinate spaces, and
it does not include the nonassociative n=8 operator bracket. -/
theorem associative_zorn_jacobi :
    (∀ x y z : F4Coordinates,
      rawJacobi LinearMap.id LinearMap.id
        (associativeValue x) (associativeValue y) (associativeValue z) = 0) ∧
    (∀ x y z : E6Coordinates,
      rawJacobi splitConjugation splitScalarPart
        (associativeValue x) (associativeValue y) (associativeValue z) = 0) ∧
    (∀ x y z : E7Coordinates,
      rawJacobi quaternionConjugation quaternionScalarPart
        (associativeValue x) (associativeValue y) (associativeValue z) = 0) := by sorry

end QAlgorithms.Papers.Independent.Support21.P05

end
