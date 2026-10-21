-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P34_coefficientSpace_intersection_integerBasis
-- name    : QAlgorithms.Papers.Independent.Next46.P34.coefficientSpace_intersection_integerBasis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:32:56.792247+00:00
-- url     : https://prove2.me/theorems/1a58afd6-2d32-4889-8a12-f75b3c6707be
-- title:
--   Coefficient space as an intersection over an integral relation basis
-- statement:
--   Let $n\geq1$ and let $X\in\operatorname{Mat}_n(\mathbb Q)$ be semisimple with square-free characteristic polynomial. Let $K/\mathbb Q$ be any finite extension containing its roots, and list its roots as $\alpha_1,\ldots,\alpha_n$. Write $t+1$ for the degree of the minimal polynomial of $X$. Define
--   $$
--   \Lambda=\{e\in\mathbb Z^n:\sum_k e_k\alpha_k=0\},\quad
--   \Lambda_{\mathbb Q}=\{e\in\mathbb Q^n:\sum_k e_k\alpha_k=0\},\quad
--   \Delta_i(e)=\sum_k e_k\alpha_k^i.
--   $$
--   Let $b_1,\ldots,b_r$ be any integral basis of the entire lattice $\Lambda$, and set
--   $$
--   M(e)=\{u\in\mathbb Q^{t+1}:\sum_{i=0}^t u_i\Delta_i(e)=0\},\qquad
--   \Upsilon=\{u\in\mathbb Q^{t+1}:\sum_{i=0}^t u_i\Delta_i(e)=0\text{ for every }e\in\Lambda_{\mathbb Q}\}.
--   $$
--   Then
--   $$
--   \Upsilon=\bigcap_{j=1}^r M(b_j).
--   $$
--   An empty intersection means all of $\mathbb Q^{t+1}$. This identity reduces the defining family of coefficient constraints to an integral basis and is independent of any approximate relation-finding procedure.
-- source:
--   Constructing algebraic Lie algebras, arXiv:math/0611414v1, PDF p. 15, §7: intersection of coefficient relation spaces

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P34

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P34

/-- Fieker–de Graaf, arXiv:math/0611414v1, PDF p.15, Section 7.
Upsilon is the intersection of M(e) for an integral basis of the full relation
lattice, in any finite extension containing the roots as in Section 3.
Printed: Q^t, indices 1,...,t, and g_i(e) = sum_k e_k x_k^n.
Changed: Q^(t+1), indices 0,...,t, and exponent i in g_i(e).
Why: Section 7 explicitly refers to Lemma 2's Upsilon and Delta_i, including
X^0. No approximate algorithm is asserted correct here. -/
theorem coefficientSpace_intersection_integerBasis
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {n : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin n) ℚ)
    (hsemisimple : Module.End.IsSemisimple (Matrix.toLin' X))
    (hsquarefree : Squarefree X.charpoly)
    (alpha : Fin n → K)
    (hroots : X.charpoly.map (algebraMap ℚ K) =
      ∏ k, (Polynomial.X - Polynomial.C (alpha k)))
    (t : ℕ) (hdegree : (minpoly ℚ X).natDegree = t + 1)
    {r : ℕ} (b : Module.Basis (Fin r) ℤ (integerRelations alpha)) :
    coefficientSpace alpha t =
      ⨅ j : Fin r, momentRelationSpace alpha t
        (fun k => (((b j : Fin n → ℤ) k) : ℚ)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P34

end
