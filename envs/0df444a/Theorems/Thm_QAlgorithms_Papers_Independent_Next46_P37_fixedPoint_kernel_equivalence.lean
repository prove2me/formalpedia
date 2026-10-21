-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P37_fixedPoint_kernel_equivalence
-- name    : QAlgorithms.Papers.Independent.Next46.P37.fixedPoint_kernel_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:40:12.951158+00:00
-- url     : https://prove2.me/theorems/bd360ffe-68a4-4db8-8d34-4ee8fece9e58
-- title:
--   Explicit isomorphism of the fixed-point and diagonal-Hessian kernels
-- statement:
--   Let $n\ge1$, let $P,Q\in M_n(\mathbb R)$ be symmetric, and let $L\in M_n(\mathbb R)$ satisfy $\det L\ne0$. Define
--
--   $$
--   S_W=\begin{pmatrix}L^{-1}Q&L^{-1}\\PL^{-1}Q-L^T&PL^{-1}\end{pmatrix},\qquad H=P+Q-L-L^T.
--   $$
--
--   There is a real linear isomorphism between the two kernels, with the following maps in grouped position and momentum coordinates:
--
--   $$
--   \ker(S_W-I)\ \xrightarrow{\ \cong\ }\ \ker H,\qquad (x,p)\longmapsto x,\qquad x\longmapsto \bigl(x,(L-Q)x\bigr).
--   $$
--
--   This identifies fixed vectors with diagonal generating-function degeneracies, including singular cases with nonzero kernels.
-- source:
--   On the Weyl Representation of Metaplectic Operators, arXiv:math/0503708v1, PDF p. 8, Remark 5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Next46.P37

/-- PDF p.8, Remark 5: the fixed-point kernel is linearly isomorphic to the
kernel of the diagonal Hessian. The forward map is position projection and the
inverse is x ↦ (x,(L-Q)x). Singular Hessians are explicitly allowed. -/
theorem fixedPoint_kernel_equivalence (n : ℕ) (hn : 0 < n)
    (P L Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hQ : Q.IsSymm) (hL : L.det ≠ 0) :
    ∃ e : LinearMap.ker (freeProjection P L Q - 1).mulVecLin ≃ₗ[ℝ]
        LinearMap.ker (diagonalHessian P L Q).mulVecLin,
      (∀ z, (e z).val = fun i => z.val (Sum.inl i)) ∧
      (∀ x, (e.symm x).val = Sum.elim x.val ((L - Q).mulVec x.val)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P37

end
