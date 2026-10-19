-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P23_sharpNuclearNormInequality
-- name    : QAlgorithms.Papers.Independent.Information100.P23.sharpNuclearNormInequality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:09:59.299963+00:00
-- url     : https://prove2.me/theorems/d5665247-b716-4aa7-ac60-1e0a66416a3d
-- title:
--   Theorem 1 (§3): sharp EB nuclear-norm inequality, including its qubit specialization
-- statement:
--   Let $d\ge1$ be an integer, and fix a basis $\lambda_1,\ldots,\lambda_{d^2-1}$ of traceless Hermitian matrices with $\operatorname{Tr}(\lambda_i\lambda_j)=2\delta_{ij}$. Let $\Phi:M_d\to M_d$ be complex linear, completely positive, trace preserving, and entanglement breaking for every finite reference system. Define its real affine Bloch data by $A_{ij}=\frac12\operatorname{Re}\operatorname{Tr}(\lambda_i\Phi(\lambda_j))$ and $c_i=\operatorname{Re}\operatorname{Tr}(\lambda_i\Phi(I/d))$. Write $\|A\|_*$ for the sum of singular values and $|c|$ for the Euclidean norm. Then
--
--   $$\|A\|_*^2+\frac{d(d-1)}2|c|^2\le(d-1)^2.$$
--
--   For $d=2$ the conclusion is $\|A\|_*^2+|c|^2\le1$. The result is a necessary EB condition with sharp attainment supplied by the next item; for $d=1$ the Bloch space is zero dimensional.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, PDF p. 2, Theorem 1 (§3): sharp EB nuclear-norm inequality, including its qubit specialization

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

/-- Theorem 1, PDF p.2, proof pp.2–3: sharp nuclear-norm inequality and its
qubit specialization. Dimension one has an empty Bloch space and is included. -/
theorem sharpNuclearNormInequality {d : ℕ} (hd : 1 ≤ d) (B : BlochBasis d)
    (Phi : ChannelMap d) (hPhi : IsCPTP Phi)
    (hEB : Entanglement.IsEntanglementBreakingPositive Phi) :
    nuclearNorm (blochA B Phi) ^ 2 + ((d : ℝ) * ((d : ℝ) - 1) / 2) *
      vectorNorm (blochC B Phi) ^ 2 ≤ ((d : ℝ) - 1) ^ 2 ∧
    (d = 2 → nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P23

end
