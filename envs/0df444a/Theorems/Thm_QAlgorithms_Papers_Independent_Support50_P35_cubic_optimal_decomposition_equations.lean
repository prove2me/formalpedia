-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_cubic_optimal_decomposition_equations
-- name    : QAlgorithms.Papers.Independent.Support50.P35.cubic_optimal_decomposition_equations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:39:44.99071+00:00
-- url     : https://prove2.me/theorems/c45f8331-ced1-4361-ac9b-3ffd7fd48545
-- title:
--   Corrected necessary cubic-circle equations
-- statement:
--   Let \(q_1=(x_1,y_1)\) and \(q_2=(x_2,y_2)\) lie on the unit circle, let \(0<p<1\), and let \(r=(r_x,r_y)\) lie in its convex hull. Suppose \(pq_1+(1-p)q_2=r\), and this decomposition attains the lower roof of \(f(x,y)=x^3\). Then
--
--   $$
--   \begin{gathered}
--   x_1^2+y_1^2-1=0,\qquad x_2^2+y_2^2-1=0,\\
--   \det\begin{pmatrix}y_1&-x_1&3x_1^2y_1\\y_2&-x_2&3x_2^2y_2\\x_1-x_2&y_1-y_2&x_1^3-x_2^3\end{pmatrix}=0,\\
--   px_1+(1-p)x_2-r_x=0,\qquad py_1+(1-p)y_2-r_y=0.
--   \end{gathered}
--   $$
--
--   The factors \(3\) correct the printed lifted derivatives in Eq.(15). These equations are necessary; they do not certify optimality.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 10, Unnumbered Eqs.(13)–(17): cubic-circle bitangent system

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.10, Eqs.(13)--(17): necessary equations for an optimal positive
2-decomposition. Eq.(15) is corrected: the two lifted derivatives have entries
3*x_j^2*y_j, not the printed x_j^2*y_j. This is not an optimality certificate. -/
theorem cubic_optimal_decomposition_equations (q : Fin 2 → (Fin 2 → ℝ))
    (p : ℝ) (hp : 0 < p ∧ p < 1) (hq : ∀ j, q j ∈ circle)
    (r : Fin 2 → ℝ) (hr : r ∈ convexHull ℝ circle)
    (hb : p • q 0 + (1 - p) • q 1 = r)
    (hopt : p * cubicCost (q 0) + (1 - p) * cubicCost (q 1) = lowerRoof circle cubicCost r) :
    q 0 0 ^ 2 + q 0 1 ^ 2 - 1 = 0 ∧
    q 1 0 ^ 2 + q 1 1 ^ 2 - 1 = 0 ∧
    Matrix.det (!![q 0 1, -q 0 0, 3 * q 0 0 ^ 2 * q 0 1;
      q 1 1, -q 1 0, 3 * q 1 0 ^ 2 * q 1 1;
      q 0 0 - q 1 0, q 0 1 - q 1 1, q 0 0 ^ 3 - q 1 0 ^ 3] : Matrix (Fin 3) (Fin 3) ℝ) = 0 ∧
    p * q 0 0 + (1 - p) * q 1 0 - r 0 = 0 ∧
    p * q 0 1 + (1 - p) * q 1 1 - r 1 = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
