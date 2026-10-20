-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P38_vectorization_partial_trace
-- name    : QAlgorithms.Papers.Independent.Dependency50.P38.vectorization_partial_trace
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:14:48.70885+00:00
-- url     : https://prove2.me/theorems/7e868047-6196-4d40-8e5d-395cfc935366
-- title:
--   Vectorization and the unnormalized partial trace
-- statement:
--   Let $a,b\geq0$ be integers and choose the standard orthonormal bases of $\mathbb C^a$ and $\mathbb C^b$. Let $M:\mathbb C^a\to\mathbb C^b$, $A:\mathbb C^a\to\mathbb C^a$, and $B:\mathbb C^b\to\mathbb C^b$ be arbitrary linear operators. Write $|V\rangle=\sum_{i=1}^b\sum_{j=1}^a M_{ij}|j\rangle\otimes|i\rangle$ for Definition 7's vectorization after the canonical tensor swap of Remark 11. Then
--
--   $$
--   \operatorname{Tr}_{\mathbb C^a}\!\left[|V\rangle\langle V|(A^{\mathsf T}\otimes B)\right]=MAM^*B.
--   $$
--
--   The trace is unnormalized, and the transpose uses the chosen bases. No positivity, unitarity, or normalization is assumed, including when either space has dimension zero. This identity translates vectorized tensors into operator expressions in the appendix's channel formulas.
-- source:
--   Classification and implementation of unitary-equivariant and permutation-invariant quantum channels, arXiv:2510.08154v1, PDF p. 34, Appendix Fact 1, Eq.(125)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P38

open scoped Matrix ComplexConjugate

/-- arXiv:2510.08154v1, PDF p.34, Appendix Fact 1, Eq.(125).
Definition 7 and Remark 11 fix the vectorization and its canonical swap.
The first tensor factor is traced without normalization. Dimensions may be
zero and M, A, B are arbitrary operators, without positivity or norm promises. -/
theorem vectorization_partial_trace (a b : ℕ)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    traceLeft (pureDensity (vectorizeInputFirst M) * Matrix.kronecker A.transpose B) =
      M * A * Mᴴ * B := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P38

end
