-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_pure_state_reduction
-- name    : SubsysAQEC.Sufficient.pure_state_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:23.088323+00:00
-- url     : https://prove2.me/theorems/3379d2ad-3bc6-4352-9832-1d55bc0ad43e
-- title:
--   p. 3, §II — the worst-case fidelity loss on the code is attained on a pure product state
-- statement:
--   Let $\mathcal E$ be a trace-preserving noise channel with Kraus operators $E_i:\mathcal H_{AB}\to\mathcal H$, and let $\{R_k\}$ be any Kraus family $\mathcal H\to\mathcal H_{AB}$ (in particular any recovery). For every code state $\rho_A\otimes\rho_B$, with $\rho_A,\rho_B$ density operators, there are unit vectors $\psi_A\in\mathcal H_A$, $\phi_B\in\mathcal H_B$ such that
--
--   $$\eta_{\mathcal R}\{\rho_A\otimes\rho_B\}\ \le\ \eta_{\mathcal R}\{|\psi_A\rangle\langle\psi_A|\otimes|\phi_B\rangle\langle\phi_B|\}.$$
--
--   Here $\eta_{\mathcal R}\{\rho\}=1-F^2(\mathrm{tr}_B\rho,\mathrm{tr}_B[(\mathcal R\circ\mathcal E)(\rho)])$ is the fidelity loss (6). Hence the maximization in (7) over the code $\mathcal C$ may be restricted to pure states on $AB$, which in $\mathcal C$ are the pure product states. The paper derives this from the joint concavity of the fidelity.
--
--   **Formalization Note** The recovery family $R$ is arbitrary (no trace-preservation is required); the claim holds for every completely positive map.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, p. 3, §II (worst-case fidelity attained on a pure state)

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix PeresTerno

theorem pure_state_reduction {a b o ι κ : Type} [Fintype a] [Fintype b] [Fintype o] [Fintype ι]
    [Fintype κ] [DecidableEq a] [DecidableEq b] [DecidableEq o]
    (E : ι → Matrix o (a × b) ℂ) (hE : IsTPNoise E) (R : κ → Matrix (a × b) o ℂ)
    (ρA : Matrix a a ℂ) (ρB : Matrix b b ℂ) (hρA : IsDensityMatrix ρA) (hρB : IsDensityMatrix ρB) :
    ∃ (ψ : a → ℂ) (φ : b → ℂ), star ψ ⬝ᵥ ψ = 1 ∧ star φ ⬝ᵥ φ = 1 ∧
      fidelityLoss E R ρA ρB ≤
        fidelityLoss E R (vecMulVec ψ (star ψ)) (vecMulVec φ (star φ)) := by sorry

end SubsysAQEC.Sufficient
