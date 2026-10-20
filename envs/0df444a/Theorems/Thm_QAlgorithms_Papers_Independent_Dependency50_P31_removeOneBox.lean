-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_removeOneBox
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.removeOneBox
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:36:01.55413+00:00
-- url     : https://prove2.me/theorems/ee0133e7-88e3-4fff-930e-d4f07b73c8c6
-- title:
--   Removing one box preserves physical Schmidt support
-- statement:
--   Let $N\ge2$, let $t$ be a standard tableau of shape $\nu$ with $N$ boxes, and let $d\ge c_1$. Let $P_t$ be the recursively defined Hermitian Young projector, and let $t^\downarrow$ be obtained by deleting the box labeled $N$. For any $\psi\in\operatorname{Im}P_t$, consider a Schmidt decomposition across the final physical factor,
--   $\psi=\sum_i\lambda_i\phi_i\otimes u_i$, with nonnegative ordered coefficients and orthonormal Schmidt families. Then
--
--   $$
--   \lambda_i>0\quad\Longrightarrow\quad \phi_i\in\operatorname{Im}P_{t^\downarrow}.
--   $$
--
--   Thus the physical Schmidt support belongs to the preceding tableau space. The assertion is homogeneous and also holds for unnormalized vectors.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 10, Corollary 7, equation (33)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Corollary 7, arXiv:1805.00364v2 PDF p.10, equation (33).
The proof constrains positive-coefficient Schmidt vectors. Arbitrary zero-coefficient
completion vectors are not constrained. The support assertion is homogeneous. -/
theorem removeOneBox {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (t : Filling n) (ht : IsTableau nu.val t) (psi : H d n)
    (hpsi : psi ∈ tableauSpace d t) (s : PhysicalSchmidtDecomposition psi (n-1) (by omega)) :
    ∀ i, 0 < s.coeff i → s.left i ∈ tableauSpace d (tableauPrefix t (n-1) (by omega)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
