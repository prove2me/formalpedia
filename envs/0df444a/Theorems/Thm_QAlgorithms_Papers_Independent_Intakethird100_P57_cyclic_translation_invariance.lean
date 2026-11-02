-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_cyclic_translation_invariance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.cyclic_translation_invariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:10:33.355221+00:00
-- url     : https://prove2.me/theorems/3557cb95-996c-4dc7-8f16-bb87c0140e00
-- title:
--   Main properties (ii): sufficient conditions for exact cyclic translation invariance
-- statement:
--   Let $N,D\ge1$ and consider the periodic trace MPS vector $M(A)$ and the RAGE vector $R(A,\Phi,V)$. Suppose that $M(A)$ is exactly invariant under one cyclic shift, that the graph weights are circulant, and that all local unitaries are the same:
--
--   $$\Phi_{j+1,k+1}=\Phi_{j,k},\qquad V_j=V_k,$$
--
--   with indices taken modulo $N$. Then
--
--   $$T R(A,\Phi,V)=R(A,\Phi,V),$$
--
--   where $T$ is the cyclic permutation of qubits. This is a sufficient condition on the underlying MPS vector, graph, and rotations; it does not require identical site tensors. It is an exact raw-vector identity and also covers $N=1$.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 2, Main properties (ii): sufficient conditions for exact cyclic translation invariance

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.2, Main properties (ii): sufficient conditions only. Invariance of the MPS
vector is assumed, rather than the narrower requirement that all tensors be equal. -/
theorem cyclic_translation_invariance {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (hA : CyclicInvariant (traceMPS A))
    (hG : ∀ i j, G.weight (nextSite i) (nextSite j) = G.weight i j)
    (hV : ∀ i j, V i = V j) : CyclicInvariant (rage A G V) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
