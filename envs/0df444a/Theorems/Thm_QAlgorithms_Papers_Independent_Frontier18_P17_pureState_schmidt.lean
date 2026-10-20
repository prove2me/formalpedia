-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_pureState_schmidt
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.pureState_schmidt
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:26:52.852978+00:00
-- url     : https://prove2.me/theorems/086f971f-ebe1-4701-9b9d-fced5e7b2d78
-- title:
--   Schmidt decomposition of a bipartite pure state
-- statement:
--   Let $m,n\ge1$ and let $\psi\in\mathbb C^m\otimes\mathbb C^n$ be a unit vector. There exist an integer $0\le k\le\min(m,n)$, positive real numbers $\lambda_1,\ldots,\lambda_k$, and orthonormal families $(\alpha_i)_{i=1}^k$ in $\mathbb C^m$ and $(\beta_i)_{i=1}^k$ in $\mathbb C^n$ such that
--
--   $$\psi=\sum_{i=1}^k\sqrt{\lambda_i}\,\alpha_i\otimes\beta_i.$$
--
--   This is the pure-state Schmidt representation. The unit-norm hypothesis and positive coefficients force $k\ge1$; no identity involving reduced ranks is asserted.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 4, Theorem 2, Eq.(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.4, Theorem 2, Eq. (19): unit state, orthonormal factors, positive
retained terms. The proof's printed second basis C^m is read as C^n. -/
theorem pureState_schmidt {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (psi : EuclideanSpace ℂ (Fin m × Fin n)) (hpsi : QAlgorithms.IsState psi) :
    ∃ (k : ℕ) (lambda : Fin k → ℝ)
      (alpha : Fin k → EuclideanSpace ℂ (Fin m))
      (beta : Fin k → EuclideanSpace ℂ (Fin n)),
      k ≤ min m n ∧ Orthonormal ℂ alpha ∧ Orthonormal ℂ beta ∧
      (∀ i, 0 < lambda i) ∧
      psi = ∑ i, (Real.sqrt (lambda i) : ℂ) • QAlgorithms.tensorVec (alpha i) (beta i) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
