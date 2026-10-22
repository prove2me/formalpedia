-- Prove2me | Theorems.Thm_QCircMITM_Search_layers_closed_under_adjoint
-- name    : QCircMITM.Search.layers_closed_under_adjoint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:09.290887+00:00
-- url     : https://prove2.me/theorems/4a382d49-ea1b-40a3-a99a-62d11dc72396
-- title:
--   Proof of Lemma 1, pp. 5–6 — V_{n,G} is closed under adjoint when G is closed under inversion
-- statement:
--   Let $\mathcal G$ be an instruction set that is closed under inversion: with every gate $g$ it contains the gate $g^\dagger$ on the same number of qubits. Let $M \in \mathcal V_{n,\mathcal G}$ be the unitary of a depth-one $n$-qubit circuit over $\mathcal G$. Then
--   $$M^\dagger \in \mathcal V_{n,\mathcal G}.$$
--   Moreover, if every gate of $\mathcal G$ is unitary, then $M$ is unitary, $M \in U(2^n)$.
--
--   This is the step "$U_1^\dagger, \dots, U_i^\dagger \in \mathcal V_{n,\mathcal G}$" in the proof of Lemma 1: it is what makes the set $S_i^\dagger$ of inverses of depth-$i$ unitaries equal to $S_i$. The unitarity clause lets $\mathcal V_{n,\mathcal G}$ (for a finite $\mathcal G$) serve as the layer set $V$ of the rest of the mission.
--
--   **Formalization Note.** Closure under inversion is `QAlgorithms.ClosedUnderInverse`, which adds $\langle k, g^\dagger\rangle$ for every gate $\langle k, g\rangle$; the adjoint of a matrix is `star`.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, pp. 5–6, proof of Lemma 1

import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QCircMITM_Search_Layers

namespace QCircMITM.Search

theorem layers_closed_under_adjoint {G : Set QAlgorithms.Gate} {n : ℕ}
    (hG : QAlgorithms.ClosedUnderInverse G)
    {M : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ} (hM : M ∈ depthOneSet G n) :
    star M ∈ depthOneSet G n ∧
      ((∀ g ∈ G, g.IsUnitary) → M ∈ Matrix.unitaryGroup (QAlgorithms.Qubits n) ℂ) := by sorry

end QCircMITM.Search
