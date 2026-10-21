-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_compact_modulus_spectral_expansion
-- name    : QAlgorithms.Papers.Independent.Next46.P02.compact_modulus_spectral_expansion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:29:38.847358+00:00
-- url     : https://prove2.me/theorems/5e6249f7-acf6-4ea7-bbe9-3f50e696f620
-- title:
--   Spectral expansion of a compact operator’s modulus
-- statement:
--   Let $T$ be a compact bounded endomorphism of a complete real or complex Hilbert space $H$. There are a complete orthonormal basis $(e_i)_{i\in I}$ of the full space and nonnegative real numbers $\mu_i$ such that, for every $x\in H$, the family below converges in Hilbert-space norm to $|T|x$:
--
--   $$
--   |T|x=\sum_{i\in I}\mu_i\langle x;e_i\rangle e_i.
--   $$
--
--   The source inner product is linear in its first argument. The basis includes a possibly nonseparable kernel and need not have a countable index set. The result diagonalizes the modulus and imposes no self-adjointness requirement on $T$.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 14, §5, Proposition 5.3: spectral expansion of the modulus of a compact operator

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.13–14, Proposition 5.3: diagonalize the modulus of a compact T on the
FULL Hilbert space, including a possibly nonseparable kernel with zero eigenvalues. -/
theorem compact_modulus_spectral_expansion (T : H →L[F] H) (hT : IsCompactOperator T) :
    ∃ (s : Set H) (b : HilbertBasis s F H) (mu : s → ℝ),
      (∀ i, 0 ≤ mu i) ∧ ∀ x : H,
        HasSum (fun i => ((mu i : F) * inner F (b i) x) • b i) (hilbertOperatorModulus T x) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
