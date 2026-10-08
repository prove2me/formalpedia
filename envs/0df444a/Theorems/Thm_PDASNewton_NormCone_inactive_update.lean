-- Prove2me | Theorems.Thm_PDASNewton_NormCone_inactive_update
-- name    : PDASNewton.NormCone.inactive_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:25.589574+00:00
-- url     : https://prove2.me/theorems/f9210520-cdcd-4596-8396-1a8b6fd40b2a
-- title:
--   Proof of Theorem 3.3, p. 8 — (yᵏ⁺¹ − ψ)_𝓘 = (yᵏ − ψ)_𝓘 + A_𝓘⁻¹A_𝓘𝓐(yᵏ − ψ)_𝓐 + A_𝓘⁻¹λᵏ_𝓘 for k ≥ 1
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a P-matrix, $f, \psi \in \mathbb{R}^n$, $c \in \mathbb{R}$, and let $(y^k, \lambda^k)_{k\ge 0}$ be a run of the primal-dual active set algorithm. For $k \ge 1$ let $\mathcal{I} = \mathcal{I}_k$ be the inactive set of $(y^k, \lambda^k)$ and $\mathcal{A} = \mathcal{A}_k$ its complement. Then
--   $$(y^{k+1} - \psi)_{\mathcal{I}} = (y^k - \psi)_{\mathcal{I}} + A_{\mathcal{I}}^{-1} A_{\mathcal{I}\mathcal{A}} (y^k - \psi)_{\mathcal{A}} + A_{\mathcal{I}}^{-1} \lambda^k_{\mathcal{I}}.$$
--   (The calligraphic $\mathcal{A}$ is an index set, distinct from the matrix $A$.)
--
--   This is the Newton update (3.3) solved for the inactive components; summing it over $\mathcal{I}$ gives (3.5), the starting point of the merit-function argument for Theorem 3.3.
--
--   **Formalization Note** The P-matrix hypothesis makes every principal block $A_{\mathcal{I}}$ invertible, so Lean's `⁻¹` is the true inverse. The restriction $k \ge 1$ is the paper's ("for $k \ge 1$ the Newton update (2.4) is equivalent to (3.3)", p. 6): it uses $Ay^k + \lambda^k = f$. The value of $c$ plays no role.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 8, proof of Theorem 3.3, first display (from (3.3), p. 6)

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_NormCone_Setting

open Filter Topology Matrix

namespace PDASNewton.NormCone

theorem inactive_update {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hA : RobinsonSR.Schur.IsPMatrix A) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ∀ S : Finset (Fin n), S = (PDASNewton.Local.activeSet c ψ (y k) (lam k))ᶜ →
      (fun i : S => y (k + 1) i - ψ i) =
        (fun i : S => y k i - ψ i) +
          (PDASNewton.MMatrix.principal A S)⁻¹ *ᵥ (PDASNewton.MMatrix.offDiag A S *ᵥ (fun j : (Sᶜ : Finset (Fin n)) => y k j - ψ j)) +
          (PDASNewton.MMatrix.principal A S)⁻¹ *ᵥ (fun i : S => lam k i) := by sorry

end PDASNewton.NormCone
