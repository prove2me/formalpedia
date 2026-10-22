-- Prove2me | Theorems.Thm_QCircMITM_Search_adjoint_layer_products
-- name    : QCircMITM.Search.adjoint_layer_products
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:13.801078+00:00
-- url     : https://prove2.me/theorems/c9b3f579-77ae-4b09-9777-452b1635d402
-- title:
--   Proof of Lemma 1, p. 5 — S†_i = S_i when the layer set is closed under adjoint
-- statement:
--   Let $V \subseteq U(2^n)$ be a finite set of $n$-qubit unitaries that is closed under adjoint ($W \in V \Rightarrow W^\dagger \in V$), and let $S_i$ be the set of products of $i$ elements of $V$ ($S_0 = \{I\}$). Then for every $i \ge 0$ and every unitary $U$,
--   $$U \in S_i^\dagger = \{\,X^\dagger : X \in S_i\,\} \iff U \in S_i ,$$
--   that is, $U^\dagger \in S_i$ if and only if $U$ can be implemented in depth $i$.
--
--   This is the observation that opens the proof of Lemma 1. With $V = \mathcal V_{n,\mathcal G}$ the hypothesis on $V$ is the previous milestone.
--
--   **Formalization Note.** $V$ stands for $\mathcal V_{n,\mathcal G}$; the statement is made for every finite set of unitaries closed under inverse, which is all the paper's argument uses. In the unitary group $U^{-1} = U^\dagger$.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 5, proof of Lemma 1

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

namespace QCircMITM.Search

theorem adjoint_layer_products {n : ℕ} (V : Finset (Unitary n)) (hV : ∀ W ∈ V, W⁻¹ ∈ V)
    (i : ℕ) (U : Unitary n) :
    U⁻¹ ∈ S V i ↔ U ∈ S V i := by sorry

end QCircMITM.Search
