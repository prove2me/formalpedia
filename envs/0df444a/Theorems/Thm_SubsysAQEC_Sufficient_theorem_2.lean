-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_theorem_2
-- name    : SubsysAQEC.Sufficient.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:23.045962+00:00
-- url     : https://prove2.me/theorems/074057a8-dfe3-4c0e-a51f-7acdf7507b7a
-- title:
--   Theorem 2, pp. 3–4 — C is ϵ-correctable on A under ℰ for ϵ ≥ η_P, with η_P given by (13)
-- statement:
--   Let $\mathcal E$ be a CPTP noise channel with Kraus operators $E_i:\mathcal H_{AB}\to\mathcal H$, $\mathcal C$ the subsystem code of all product states $\rho_A\otimes\rho_B$, and suppose
--   $$PE_i^\dagger\mathcal E(P)^{-1/2}E_jP=P_A\otimes B_{ij}+\Delta_{ij}\qquad(12)$$
--   for all $i,j$, with $B_{ij}\in\mathcal B(\mathcal H_B)$ and $\Delta_{ij}\in\mathcal B(\mathcal H_{AB})$. Define
--   $$\eta_P\equiv\max_{|\psi_A,\phi_B\rangle}\langle\phi_B|\sum_{ij}\Big[\langle\psi_A|\Delta^\dagger_{ij}\Delta_{ij}|\psi_A\rangle-\langle\psi_A|\Delta^\dagger_{ij}|\psi_A\rangle\langle\psi_A|\Delta_{ij}|\psi_A\rangle\Big]|\phi_B\rangle.\qquad(13)$$
--   Then:
--
--   1. at every pure product code state $|\psi_A\rangle\langle\psi_A|\otimes|\phi_B\rangle\langle\phi_B|$ the fidelity loss of the transpose channel $\mathcal R_P$ equals the expression maximized in (13);
--   2. for every $\epsilon\ge\eta_P$, the code $\mathcal C$ is $\epsilon$-correctable on $A$ under $\mathcal E$, and indeed the transpose channel has fidelity loss at most $\epsilon$ on every code state $\rho_A\otimes\rho_B$, mixed states included.
--
--   This is the paper's quantitative sufficient condition for approximate subsystem codes, relating the size of the perturbation $\Delta_{ij}$ of the perfect-correction condition (11) to $\epsilon$.
--
--   **Formalization Note** "$\epsilon\ge\eta_P$" is encoded as "$\epsilon$ is at least the expression (13) at every pair of unit vectors", which avoids a supremum; part 1 says the expression is the transpose channel's fidelity loss, so the maximum in (13) is the fidelity loss $\eta_P$ over pure product states. The decomposition (12) is arbitrary: the theorem holds for every choice of $B_{ij}$, with $\Delta_{ij}$ then determined.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, pp. 3–4, Theorem 2, (12)–(13)

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix QReversal.NearOpt PeresTerno
open scoped Kronecker

theorem theorem_2 {a b o ι : Type} [Fintype a] [Fintype b] [Fintype o] [Fintype ι]
    [DecidableEq a] [DecidableEq b] [DecidableEq o]
    (E : ι → Matrix o (a × b) ℂ) (hE : IsTPNoise E)
    (B : ι → ι → Matrix b b ℂ) (Δ : ι → ι → Matrix (a × b) (a × b) ℂ)
    (h12 : ∀ i j, (E i)ᴴ * invSqrt (noiseOfP E) * E j = (1 : Matrix a a ℂ) ⊗ₖ B i j + Δ i j) :
    (∀ (ψ : a → ℂ) (φ : b → ℂ), star ψ ⬝ᵥ ψ = 1 → star φ ⬝ᵥ φ = 1 →
      fidelityLoss E (transposeKraus E) (vecMulVec ψ (star ψ)) (vecMulVec φ (star φ)) =
        eq13Summand Δ ψ φ) ∧
    ∀ ε : ℝ, (∀ (ψ : a → ℂ) (φ : b → ℂ), star ψ ⬝ᵥ ψ = 1 → star φ ⬝ᵥ φ = 1 →
        eq13Summand Δ ψ φ ≤ ε) →
      IsEpsCorrectable E ε ∧
        ∀ (ρA : Matrix a a ℂ) (ρB : Matrix b b ℂ), IsDensityMatrix ρA → IsDensityMatrix ρB →
          fidelityLoss E (transposeKraus E) ρA ρB ≤ ε := by sorry

end SubsysAQEC.Sufficient
