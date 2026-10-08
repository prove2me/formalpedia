-- Prove2me | Theorems.Thm_PDASNewton_Perturb_principal_inv_offDiag_le
-- name    : PDASNewton.Perturb.principal_inv_offDiag_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:43.888446+00:00
-- url     : https://prove2.me/theorems/61ed80f7-5e2e-467d-908d-cca1fbee8cf0
-- title:
--   Proof of Theorem 3.4, p. 9 — A_𝓘⁻¹A_𝓘𝓐 ≤ M_𝓘⁻¹K_𝓘𝓐 − M_𝓘⁻¹K_𝓘(M + K)_𝓘⁻¹A_𝓘𝓐
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be an M-matrix, $K \in \mathbb{R}^{n\times n}$ and $A = M+K$. Let $\mathcal{I} \subseteq \{1,\dots,n\}$ be an index set with complement $\mathcal{A}$ (an index set, not the matrix $A$), and suppose the principal block $A_{\mathcal{I}} = (M+K)_{\mathcal{I}}$ is invertible. Then, entrywise,
--   $$A_{\mathcal{I}}^{-1}A_{\mathcal{I}\mathcal{A}} \;\le\; M_{\mathcal{I}}^{-1}K_{\mathcal{I}\mathcal{A}} - M_{\mathcal{I}}^{-1}K_{\mathcal{I}}(M+K)_{\mathcal{I}}^{-1}A_{\mathcal{I}\mathcal{A}} .$$
--
--   The bound isolates the effect of the perturbation $K$ on the off-diagonal coupling term of (3.8): its right-hand side is of order $\|K\|_1$, which is what allows $\|K\|_1$ to be chosen so small that $\sum_i y^k_i$ is a merit function.
--
--   **Formalization Note** The invertibility of $(M+K)_{\mathcal{I}}$ is a hypothesis because Lean's inverse of a singular matrix is $0$, which would change the meaning of the inequality; in the paper it holds for small $\|K\|_1$ by the Neumann-series step. The page's justification uses $(M+K)_{\mathcal{I}}^{-1} - M_{\mathcal{I}}^{-1} = -M_{\mathcal{I}}^{-1}K_{\mathcal{I}}(M+K)_{\mathcal{I}}^{-1}$ and $M_{\mathcal{I}}^{-1}M_{\mathcal{I}\mathcal{A}} \le 0$.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 9, proof of Theorem 3.4, last paragraph ("Note that A_𝓘⁻¹A_𝓘𝓐 ≤ …")

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

open Filter Topology Matrix

namespace PDASNewton.Perturb

theorem principal_inv_offDiag_le {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℝ) (hM : IsMMatrix M)
    (S : Finset (Fin n)) (hA : IsUnit (PDASNewton.MMatrix.principal (M + K) S).det) :
    ∀ i j, ((PDASNewton.MMatrix.principal (M + K) S)⁻¹ * PDASNewton.MMatrix.offDiag (M + K) S) i j ≤
      ((PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.offDiag K S -
        (PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S * (PDASNewton.MMatrix.principal (M + K) S)⁻¹ * PDASNewton.MMatrix.offDiag (M + K) S) i j := by sorry

end PDASNewton.Perturb
