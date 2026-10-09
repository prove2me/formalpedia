-- Prove2me | Theorems.Thm_PinningSync_Strong_lemma_2_12
-- name    : PinningSync.Strong.lemma_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:24.822584+00:00
-- url     : https://prove2.me/theorems/71d35731-c575-4b7d-8932-3736f7dcd02d
-- title:
--   Lemma 2.12, p. 1401 — a positive diagonal Ξ makes Ĝ = ½(ΞG + GᵀΞ) symmetric with zero row and column sums
-- statement:
--   Let $G$ be an irreducible coupling matrix ($G_{ij}\ge 0$ for $i\ne j$, $\sum_j G_{ij}=0$). Then there is a positive definite diagonal matrix $\Xi=\operatorname{diag}(\xi_1,\dots,\xi_N)$ (all $\xi_i>0$) such that
--   $$
--   \widehat G=\tfrac12\bigl(\Xi G+G^T\Xi\bigr)
--   $$
--   is symmetric and
--   $$
--   \sum_{j=1}^N\widehat G_{ij}=\sum_{j=1}^N\widehat G_{ji}=0\qquad(i=1,\dots,N).
--   $$
--
--   This weighting is what makes the Lyapunov functional $V=\tfrac12\sum_i\xi_ie_i^Te_i$ of Theorem 3.1 work on a directed network: $\widehat G$ is a symmetric matrix of the form (2.2).
--
--   **Formalization Note.** $\Xi$ is encoded by the vector $\xi$ of its diagonal entries; "positive definite diagonal" is $\xi_i>0$ for all $i$.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1401, Lemma 2.12

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSync.Strong

open Matrix

theorem lemma_2_12 {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsCouplingMatrix G)
    (hirr : IsIrred G) :
    ∃ ξ : Fin N → ℝ, (∀ i, 0 < ξ i) ∧ (Ghat G ξ)ᵀ = Ghat G ξ ∧
      (∀ i, ∑ j, Ghat G ξ i j = 0) ∧ (∀ i, ∑ j, Ghat G ξ j i = 0) := by sorry

end PinningSync.Strong
