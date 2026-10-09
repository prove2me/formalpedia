-- Prove2me | Theorems.Thm_TroppMatrixConcentration_dilation_identities
-- name    : TroppMatrixConcentration.dilation_identities
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:50:37.865108+00:00
-- url     : https://prove2.me/theorems/0d005fd8-b32e-43ea-bbc1-b212cd2b89a3
-- title:
--   Equations 2.1.27–2.1.28 — Hermitian dilation identities
-- statement:
--   Let $A$ be a complex $m\times n$ matrix, with $m,n\ge1$, and set $H(A)=\begin{pmatrix}0&A\\A^*&0\end{pmatrix}$. Then $H(A)$ is Hermitian and
--   $$H(A)^2=\begin{pmatrix}AA^*&0\\0&A^*A\end{pmatrix},\qquad \lambda_{\max}(H(A))=\|H(A)\|=\|A\|.$$
--   Here all norms are spectral norms. The identities relate rectangular matrices to a Hermitian matrix of dimension $m+n$.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Definition 2.1.5 and equations (2.1.27–28), printed pp. 24–25.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem dilation_identities {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (dilation A).IsHermitian ∧
    (dilation A) ^ 2 = Matrix.fromBlocks (A * A.conjTranspose) 0 0
      (A.conjTranspose * A) ∧
    lambdaMax (dilation A) = spectralNorm (dilation A) ∧
    spectralNorm (dilation A) = spectralNorm A := by sorry

end TroppMatrixConcentration
