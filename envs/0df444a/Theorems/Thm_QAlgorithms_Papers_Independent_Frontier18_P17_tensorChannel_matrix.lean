-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_tensorChannel_matrix
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.tensorChannel_matrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:33:09.438063+00:00
-- url     : https://prove2.me/theorems/c665f437-de3e-42e2-be39-9118c85958f1
-- title:
--   Matrix representation of parallel channel composition
-- statement:
--   Let $m,n\ge1$, and let $\Phi$ on $M_m(\mathbb C)$ and $\Psi$ on $M_n(\mathbb C)$ be complex-linear completely positive trace-preserving maps. Define $\Phi\otimes\Psi$ independently by its action $E_{aa'}\otimes E_{bb'}\mapsto\Phi(E_{aa'})\otimes\Psi(E_{bb'})$, extended linearly to every operator. Let $M_\Theta$ be the matrix of a map $\Theta$ in row-stacked coordinates. Let $P$ send the coordinate index $((a,b),(a',b'))$ to $((a,a'),(b,b'))$, and let $P^{-1}$ be its inverse. Then
--
--   $$M_{\Phi\otimes\Psi}=P^{-1}(M_\Phi\otimes M_\Psi)P.$$
--
--   This is a representation formula for parallel application to an arbitrary bipartite operator. It retains the inverse for unequal subsystem dimensions.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 8, §IV C, Definition 11, Eq.(63)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.8, Definition 11, Eq. (63): parallel tensor composition, with the
inverse reshuffling permutation retained for general subsystem dimensions. -/
theorem tensorChannel_matrix {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (Phi : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (Psi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hPhi : CPTP Phi) (hPsi : CPTP Psi) :
    superMatrix (tensorMap Phi Psi) = unreshuffleMatrix (Fin m) (Fin n) *
      Matrix.kronecker (superMatrix Phi) (superMatrix Psi) * reshuffleMatrix (Fin m) (Fin n) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
