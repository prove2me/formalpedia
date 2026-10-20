-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_density_operatorSchmidt
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.density_operatorSchmidt
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:30:08.597361+00:00
-- url     : https://prove2.me/theorems/46096532-8e86-469f-b441-0c8ebfc11509
-- title:
--   Operator Schmidt decomposition using the printed coefficient array
-- statement:
--   Let $m,n\ge1$ and let $\rho$ be any positive semidefinite, trace-one operator on $\mathbb C^m\otimes\mathbb C^n$. Let $(E_a)_{a=1}^{m^2}$ and $(F_b)_{b=1}^{n^2}$ be the canonical matrix units in row order. Set $C_{ab}=\operatorname{tr}(\rho^\dagger(E_a\otimes F_b))$. There exist $k\le\min(m^2,n^2)$, positive singular values $\sigma_i$, and orthonormal left and right singular-vector families $u_i\in\mathbb C^{m^2}$, $v_i\in\mathbb C^{n^2}$ giving a complete thin SVD, such that
--
--   $$C=\sum_{i=1}^k\sigma_i u_i v_i^\dagger,\qquad
--   \rho=\sum_{i=1}^k\sigma_i\operatorname{unres}(\overline{u_i})\otimes\operatorname{unres}(v_i).$$
--
--   Here $\operatorname{unres}$ is inverse row reshaping. The resulting local operator families are orthonormal for the Hilbert–Schmidt product; they need not be positive, Hermitian, or normalized density matrices. This representation applies to all bipartite states, including entangled states.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 5, §III C, Eqs.(30)–(31)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.5, Eqs. (30)–(31): operator Schmidt decomposition of a full bipartite
state. Conjugate the left SVD vectors of the printed array to reconstruct rho.
Factors are HS-orthonormal and need not be Hermitian, positive or trace one. -/
theorem density_operatorSchmidt {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) :
    ∃ (k : ℕ) (s : Fin k → ℝ)
      (u : Fin k → EuclideanSpace ℂ (Fin m × Fin m))
      (v : Fin k → EuclideanSpace ℂ (Fin n × Fin n)),
      k ≤ min (m*m) (n*n) ∧ ThinSVD (operatorCoefficients rho) s u v ∧
      rho = ∑ i, (s i : ℂ) • Matrix.kronecker
        (unres (WithLp.toLp 2 (fun a => conj (u i a)))) (unres (v i)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
