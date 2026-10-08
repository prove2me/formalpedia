-- Prove2me | Theorems.Thm_PDASNewton_Perturb_isMMatrix_principal
-- name    : PDASNewton.Perturb.isMMatrix_principal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:16.977832+00:00
-- url     : https://prove2.me/theorems/5c5b21e1-9269-4915-9d13-ce6b3a2162a4
-- title:
--   Proof of Theorem 3.4, p. 9 — principal submatrices of an M-matrix are nonsingular M-matrices
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be an M-matrix: nonsingular, with $m_{ij} \le 0$ for $i \ne j$ and $M^{-1} \ge 0$ entrywise. Then for every index set $\mathcal{I} \subseteq \{1,\dots,n\}$ the principal submatrix $M_{\mathcal{I}} = (m_{ij})_{i,j\in\mathcal{I}}$ is again an M-matrix:
--   $$M_{\mathcal{I}} \text{ is nonsingular}, \qquad (M_{\mathcal{I}})_{ij} \le 0 \ (i \ne j), \qquad M_{\mathcal{I}}^{-1} \ge 0 .$$
--
--   The proof of Theorem 3.4 recalls this classical fact from Berman and Plemmons; it makes every $M_{\mathcal{I}}^{-1}$ exist and be nonnegative, which the Neumann-series representation of $A_{\mathcal{I}}^{-1}$ and the estimates of the proof rely on.
--
--   **Formalization Note** The index set is any `Finset (Fin n)`, including the empty set (for which the empty matrix is trivially an M-matrix) and the full set.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 9, proof of Theorem 3.4, first sentence (citing [BP])

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

open Filter Topology Matrix

namespace PDASNewton.Perturb

theorem isMMatrix_principal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsMMatrix M) :
    ∀ S : Finset (Fin n), IsMMatrix (PDASNewton.MMatrix.principal M S) := by sorry

end PDASNewton.Perturb
