-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_real_clifford_type_table
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.real_clifford_type_table
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:01:09.411412+00:00
-- url     : https://prove2.me/theorems/69f9d46a-e9be-40aa-ace1-77194280484b
-- title:
--   Proposition 1.7
-- statement:
--   For $p+q>0$, the graded type of the real Clifford algebra $\operatorname{Cl}_{p,q}=\operatorname{Cl}(\mathbb R^{p,q},-g)$ is the ordered pair consisting of its even-subalgebra type and its full-algebra type. A type $K$ means $\operatorname{Mat}_k(K)$ for some positive integer $k$, and $2K$ means two copies of such a matrix algebra. The complete table, with $s=p-q$ read modulo eight, is
--   $$\begin{array}{c|cccccccc}s&1&2&3&4&5&6&7&0\\\hline t(s)&(R,C)&(C,H)&(H,2H)&(2H,H)&(H,C)&(C,R)&(R,2R)&(2R,R)\end{array}$$
--   Here $R=\mathbb R$, $C=\mathbb C$, and $H=\mathbb H$; every type assertion means real algebra isomorphism. This table records both algebras rather than only their dimensions.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 15, Proposition 1.7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Proposition 1.7, PDF p. 15: all eight even/full real algebra types, with positive matrix size. -/
theorem real_clifford_type_table (p q : ℕ) (hd : 0 < p + q) :
    HasRealGradedType p q (realTypeTable ((p : ℤ) - q)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
