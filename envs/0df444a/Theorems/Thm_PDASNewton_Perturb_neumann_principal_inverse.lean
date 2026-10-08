-- Prove2me | Theorems.Thm_PDASNewton_Perturb_neumann_principal_inverse
-- name    : PDASNewton.Perturb.neumann_principal_inverse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:09.280781+00:00
-- url     : https://prove2.me/theorems/8f12161d-73f8-4f29-b34d-38d7fa281ff8
-- title:
--   Proof of Theorem 3.4, p. 9 — for ρ < ½, A_𝓘 = (M+K)_𝓘 is invertible and A_𝓘⁻¹ = (I_𝓘 + Σᵢ≥₁(−M_𝓘⁻¹K_𝓘)ⁱ)M_𝓘⁻¹
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be an M-matrix, $K \in \mathbb{R}^{n\times n}$ arbitrary, and $A = M + K$. Let $\rho \in \mathbb{R}$ be an upper bound of $\|M_{\mathcal{I}}^{-1}K_{\mathcal{I}}\|_1$ over all index sets $\mathcal{I} \subseteq \{1,\dots,n\}$ (for instance $\rho = \sup_{\mathcal{I}} \|M_{\mathcal{I}}^{-1}K_{\mathcal{I}}\|_1$), where $\|\cdot\|_1$ is the maximal absolute column sum, and suppose $\rho < \tfrac12$. Then for every $\mathcal{I}$ the principal block $A_{\mathcal{I}} = (M+K)_{\mathcal{I}}$ is invertible and
--   $$A_{\mathcal{I}}^{-1} = \Big(I_{\mathcal{I}} + \sum_{i=1}^{\infty} \big(-M_{\mathcal{I}}^{-1}K_{\mathcal{I}}\big)^i\Big) M_{\mathcal{I}}^{-1},$$
--   the series converging.
--
--   Since every $A_{\mathcal{I}}$ is invertible, each step of the primal-dual active set algorithm has exactly one solution: the algorithm is well-defined.
--
--   **Formalization Note** The series is written from $i = 0$, the term $i = 0$ being $I_{\mathcal{I}} M_{\mathcal{I}}^{-1}$; convergence is `HasSum` in the entrywise topology of matrices. Taking $\rho$ to be any bound of the family rather than its supremum is equivalent for this statement and avoids a supremum over an index type.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 9, proof of Theorem 3.4, definition of ρ and display of A_𝓘⁻¹

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

open Filter Topology Matrix

namespace PDASNewton.Perturb

theorem neumann_principal_inverse {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℝ) (hM : IsMMatrix M)
    (ρ : ℝ) (hρ : ∀ S : Finset (Fin n), oneNorm ((PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S) ≤ ρ)
    (hρ_half : ρ < 1 / 2) :
    ∀ S : Finset (Fin n), IsUnit (PDASNewton.MMatrix.principal (M + K) S).det ∧
      HasSum (fun i : ℕ => (-((PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S)) ^ i * (PDASNewton.MMatrix.principal M S)⁻¹)
        (PDASNewton.MMatrix.principal (M + K) S)⁻¹ := by sorry

end PDASNewton.Perturb
