-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_corollary_3_bound
-- name    : SubsysAQEC.Sufficient.corollary_3_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:18.234226+00:00
-- url     : https://prove2.me/theorems/46d27f5c-c92e-49e7-96fe-a5e1e61a568f
-- title:
--   Proof of Corollary 3, p. 4 — the expression (13) is at most ‖Σ_ij Δ_ij^† Δ_ij‖
-- statement:
--   Let $\Delta_{ij}$ be any finite family of operators on $\mathcal H_{AB}$, and $\psi_A,\phi_B$ unit vectors. The expression maximized in (13) at the pure product state $|\psi_A,\phi_B\rangle$ satisfies
--
--   $$\langle\phi_B|\sum_{ij}\Big[\langle\psi_A|\Delta^\dagger_{ij}\Delta_{ij}|\psi_A\rangle-\langle\psi_A|\Delta^\dagger_{ij}|\psi_A\rangle\langle\psi_A|\Delta_{ij}|\psi_A\rangle\Big]|\phi_B\rangle\ \le\ \langle\psi_A,\phi_B|\sum_{ij}\Delta^\dagger_{ij}\Delta_{ij}|\psi_A,\phi_B\rangle\ \le\ \Big\|\sum_{ij}\Delta^\dagger_{ij}\Delta_{ij}\Big\|,$$
--
--   where $\|\cdot\|$ is the operator norm (largest singular value). Hence $\eta_P\le\|\sum_{ij}\Delta^\dagger_{ij}\Delta_{ij}\|$.
--
--   **Formalization Note** The operator norm is Mathlib's $\ell^2$ operator norm on matrices (`Matrix.Norms.L2Operator`), not the entrywise or Frobenius norm.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, p. 4, proof of Corollary 3

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix
open scoped Matrix.Norms.L2Operator

theorem corollary_3_bound {a b ι : Type} [Fintype a] [Fintype b] [Fintype ι]
    [DecidableEq a] [DecidableEq b]
    (Δ : ι → ι → Matrix (a × b) (a × b) ℂ) (ψ : a → ℂ) (φ : b → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1) :
    eq13Summand Δ ψ φ ≤
        (star (prodVec ψ φ) ⬝ᵥ ((∑ i, ∑ j, (Δ i j)ᴴ * Δ i j) *ᵥ prodVec ψ φ)).re ∧
      (star (prodVec ψ φ) ⬝ᵥ ((∑ i, ∑ j, (Δ i j)ᴴ * Δ i j) *ᵥ prodVec ψ φ)).re ≤
        ‖∑ i, ∑ j, (Δ i j)ᴴ * Δ i j‖ := by sorry

end SubsysAQEC.Sufficient
