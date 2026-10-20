-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_partialChannel_matrix
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.partialChannel_matrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:33:57.856701+00:00
-- url     : https://prove2.me/theorems/f8439a74-738f-4f44-a4ad-795ff7e7eb77
-- title:
--   Matrix representation of partial channel application
-- statement:
--   Let $m,n\ge1$ and let $\Phi:M_m(\mathbb C)\to M_m(\mathbb C)$ be complex-linear, completely positive and trace preserving. Its partial application $\Phi\otimes\mathrm{id}_n$ is extended from matrix units to all operators on $\mathbb C^m\otimes\mathbb C^n$. In row-stacked coordinates let $M_\Phi$ be the local matrix and let $P$ regroup $((a,b),(a',b'))$ as $((a,a'),(b,b'))$. Then
--
--   $$M_{\Phi\otimes\mathrm{id}_n}=P^{-1}(M_\Phi\otimes I_{n^2})P.$$
--
--   This represents an operation on the first subsystem while leaving the second unchanged, including for entangled input states. The identity acts on the $n^2$-dimensional operator space.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 8, §IV D; Appendix A.3.b, PDF p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.8, Section IV D; p.10, Appendix A.3.b: partial application on all
operators; the identity matrix on the untouched operator space has dimension n^2. -/
theorem partialChannel_matrix {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (Phi : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hPhi : CPTP Phi) :
    superMatrix (tensorMap Phi (LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)) =
      unreshuffleMatrix (Fin m) (Fin n) *
        Matrix.kronecker (superMatrix Phi) (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) *
        reshuffleMatrix (Fin m) (Fin n) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
