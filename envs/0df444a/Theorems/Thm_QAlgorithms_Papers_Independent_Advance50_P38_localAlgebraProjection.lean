-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_localAlgebraProjection
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.localAlgebraProjection
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:44:59.901991+00:00
-- url     : https://prove2.me/theorems/69e1a597-20ed-4e0a-9095-ca1fcb94cb01
-- title:
--   Corollary III.6: local algebra projection
-- statement:
--   Let $n\ge1$ and let $X_k,Y_k,Z_k$ be the skew-Hermitian generators acting in tensor position $k$, with identity factors elsewhere. Their one-qubit matrices are $X=\left(\begin{smallmatrix}0&i\\i&0\end{smallmatrix}\right)$, $Y=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ and $Z=\operatorname{diag}(i,-i)$. For the real Hilbert–Schmidt inner product, the unique projection onto $\mathfrak{su}_{\mathrm{loc}}(2^n)$ is
--   $$P g=2^{-n}\sum_{k=1}^n\bigl(\langle g,X_k\rangle X_k+\langle g,Y_k\rangle Y_k+\langle g,Z_k\rangle Z_k\bigr).$$
--   This applies to every complex $2^n$ by $2^n$ matrix, not just skew-Hermitian matrices.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 22, Corollary III.6: local algebra projection

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Corollary III.6, PDF p.22: real projection of all complex matrices. -/
theorem localAlgebraProjection {n : ℕ} (hn : 0 < n)
    (g : Matrix (LocalQubitIndex n) (LocalQubitIndex n) ℂ) :
    (∃! p, IsHSProjection (localAlgebra n : Set _) g p) ∧
    IsHSProjection (localAlgebra n : Set _) g (localProjection g) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
