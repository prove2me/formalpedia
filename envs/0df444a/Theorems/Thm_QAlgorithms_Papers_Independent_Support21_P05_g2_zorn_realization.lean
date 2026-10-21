-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P05_g2_zorn_realization
-- name    : QAlgorithms.Papers.Independent.Support21.P05.g2_zorn_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:31:54.505371+00:00
-- url     : https://prove2.me/theorems/0ae44d59-9ec3-4014-9e1c-93d4993bd6e1
-- title:
--   G2 realized by the closed special Zorn commutator
-- statement:
--   All vector spaces are over the base field $\mathbb C$. Let $\mathfrak g_2$ denote the split complex exceptional Lie algebra of type $G_2$, independently defined by its Serre presentation. Set $Z_2=\mathfrak{sl}_3(\mathbb C)\oplus\mathbb C^3\oplus(\mathbb C^3)^*$, writing an element as $(a,A^+,A^-)$. Rows and columns have ordinary complex-bilinear contraction, with no scalar conjugation. Let $v\wedge w$ be the oriented three-dimensional cross product and $v\circ w=(\sum_i v_iw_i)I_3-3(v_iw_j)_{ij}$. Define the special bracket by
--
--   $$
--   [(a,A^+,A^-),(b,B^+,B^-)]_Z=\bigl([a,b]+A^+\circ B^- -B^+\circ A^-,\ aB^+-bA^++2A^-\wedge B^-,\ A^-b-B^-a+2A^+\wedge B^+\bigr).
--   $$
--
--   There is a complex-linear bijection $\rho:\mathfrak g_2\to Z_2$ such that
--
--   $$\rho([X,Y])=[\rho(X),\rho(Y)]_Z\qquad(X,Y\in\mathfrak g_2).$$
--
--   Thus the special Zorn commutator realizes the full adjoint Lie algebra. Its multiplication is the specified nonstandard operation.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations, arXiv:1403.5120v2, PDF p. 11, §4, (4.4)–(4.7): G2 Lie realization

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P05

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

/-- §§4, (4.4)–(4.7), PDF pp. 9–11: the special bracket realizes the independently
Serre-defined complex g2. No ordinary 4 by 4 associative representation is asserted. -/
theorem g2_zorn_realization :
    ∃ rho : LieAlgebra.g₂ ℂ ≃ₗ[ℂ] G2Coordinates,
      ∀ x y, g2Value (rho ⁅x, y⁆) = g2Bracket (g2Value (rho x)) (g2Value (rho y)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P05

end
