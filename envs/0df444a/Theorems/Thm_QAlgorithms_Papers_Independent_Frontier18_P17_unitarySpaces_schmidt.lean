-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_unitarySpaces_schmidt
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.unitarySpaces_schmidt
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:29:10.247973+00:00
-- url     : https://prove2.me/theorems/457aa722-1464-4db9-a5ff-1a42b20b9c80
-- title:
--   Schmidt decomposition in finite complex inner-product spaces
-- statement:
--   Let $H_A,H_B$ be finite-dimensional complex inner-product spaces, with the induced inner product on their tensor product, and let $v\in H_A\otimes H_B$ be arbitrary. There exist $0\le k\le\min(\dim H_A,\dim H_B)$, positive real numbers $\lambda_i$, and orthonormal families $u_i\in H_A$, $w_i\in H_B$, indexed by $1\le i\le k$, such that
--
--   $$v=\sum_{i=1}^k\sqrt{\lambda_i}\,u_i\otimes w_i.$$
--
--   This extends Schmidt decomposition beyond normalized quantum states. The zero vector, including in zero-dimensional spaces, is represented by the empty sum.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 4, Theorem 4, Eq.(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.4, Theorem 4, Eq. (26): arbitrary finite complex inner-product spaces.
No normalization; zero and zero-dimensional spaces admit the empty sum.
As in Theorem 2, sqrt(lambda), not lambda, is a singular value. -/
theorem unitarySpaces_schmidt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (v : E ⊗[ℂ] F) :
    ∃ (k : ℕ) (lambda : Fin k → ℝ) (u : Fin k → E) (w : Fin k → F),
      k ≤ min (Module.finrank ℂ E) (Module.finrank ℂ F) ∧
      Orthonormal ℂ u ∧ Orthonormal ℂ w ∧ (∀ i, 0 < lambda i) ∧
      v = ∑ i, (Real.sqrt (lambda i) : ℂ) • (u i ⊗ₜ[ℂ] w i) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
